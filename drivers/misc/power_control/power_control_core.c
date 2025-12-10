// SPDX-License-Identifier: GPL-2.0
/*
 * power_control_core.c - Balanced power control core for aggressive energy saving
 *
 * Features:
 *  - persistent / temp limit APIs
 *  - conservative "nyako" power clamp (with override threshold)
 *  - exports fg_pid and screen_on getters for strategy module
 *  - de-duplicates persistent limit requests
 *
 * Note: fully event-driven, no polling or kthreads
 */

#include <linux/module.h>
#include <linux/init.h>
#include <linux/kobject.h>
#include <linux/sysfs.h>
#include <linux/string.h>
#include <linux/cpufreq.h>
#include <linux/workqueue.h>
#include <linux/mutex.h>
#include <linux/slab.h>
#include <linux/jiffies.h>
#include <linux/printk.h>
#include <linux/types.h>
#include <linux/sched.h>
#include <linux/cpumask.h>

#define PC_BOOST_LIST_MAX 4096

/* conservative nyako thresholds */
#define NYAKO_POWER_LIMIT_MW        2100
#define NYAKO_OVERRIDE_NO_LIMIT_MW  4000
#define NYAKO_LOCK_MS               10000

static unsigned long nyako_lock_jiffies;
static unsigned int nyako_locked_khz;

int pc_perf_mode = 1;
unsigned int pc_cpu_limit_khz;
unsigned int pc_big_task_thresh = 60;
int pc_nyako_enabled = 1;

EXPORT_SYMBOL_GPL(pc_perf_mode);
EXPORT_SYMBOL_GPL(pc_cpu_limit_khz);
EXPORT_SYMBOL_GPL(pc_big_task_thresh);
EXPORT_SYMBOL_GPL(pc_nyako_enabled);

/* foreground pid and screen_on state */
static pid_t pc_fg_pid = 0;
static bool pc_screen_on = true;
static DEFINE_MUTEX(pc_fg_lock);

/* getters for other modules */
pid_t pc_get_fg_pid(void) { return READ_ONCE(pc_fg_pid); }
bool pc_is_screen_on(void) { return READ_ONCE(pc_screen_on); }
EXPORT_SYMBOL_GPL(pc_get_fg_pid);
EXPORT_SYMBOL_GPL(pc_is_screen_on);

/* sysfs and workqueue */
static struct kobject *pc_kobj;
static struct workqueue_struct *pc_wq;
static DEFINE_MUTEX(pc_lock);

static char pc_boost_list[PC_BOOST_LIST_MAX];

bool boost_list_contains(const char *name)
{
    if (!name || !pc_boost_list[0])
        return false;
    if (strnstr(pc_boost_list, name, PC_BOOST_LIST_MAX))
        return true;
    return false;
}
EXPORT_SYMBOL_GPL(boost_list_contains);

/* simple freq->power mapping */
static inline unsigned int current_power_mw(void)
{
    int cpu;
    unsigned int total_mw = 0, f, mw;
    struct cpufreq_policy *policy;

    for_each_online_cpu(cpu) {
        policy = cpufreq_cpu_get(cpu);
        if (!policy) continue;
        f = cpufreq_quick_get(cpu);
        if (f <= 600000)      mw = 150;
        else if (f <= 900000) mw = 350;
        else if (f <= 1200000)mw = 700;
        else if (f <= 1500000)mw = 1100;
        else                  mw = 1400;
        total_mw += mw;
        cpufreq_cpu_put(policy);
    }
    return total_mw;
}

/* decide frequency with nyako clamp */
static unsigned int pc_power_limited_khz(unsigned int req_khz)
{
    unsigned long now = jiffies;
    unsigned int cur_mw;

    if (!pc_nyako_enabled)
        return req_khz;

    cur_mw = current_power_mw();

    if (cur_mw >= NYAKO_OVERRIDE_NO_LIMIT_MW) {
        nyako_locked_khz = 0;
        nyako_lock_jiffies = now;
        return req_khz;
    }

    if (time_before(now, nyako_lock_jiffies + msecs_to_jiffies(NYAKO_LOCK_MS))) {
        if (nyako_locked_khz) return nyako_locked_khz;
        return req_khz;
    }

    if (cur_mw > NYAKO_POWER_LIMIT_MW) {
        nyako_locked_khz = 600000;
        nyako_lock_jiffies = now;
        pr_info("pc: nyako engaged limit=%ukHz power=%umW\n", nyako_locked_khz, cur_mw);
        return nyako_locked_khz;
    }

    nyako_locked_khz = 0;
    nyako_lock_jiffies = now;
    if (req_khz > 1200000)
        req_khz = 1200000;
    return req_khz;
}

/* work structure for freq requests */
struct pc_freq_request {
    struct work_struct work;
    unsigned int khz;
};

static void pc_apply_work(struct work_struct *work)
{
    struct pc_freq_request *req = container_of(work, struct pc_freq_request, work);
    int cpu;
    struct cpufreq_policy *policy;
    unsigned int target_khz;

    for_each_online_cpu(cpu) {
        policy = cpufreq_cpu_get(cpu);
        if (!policy) continue;
        target_khz = pc_power_limited_khz(req->khz);
        if (target_khz == 0)
            target_khz = policy->cpuinfo.max_freq;
        cpufreq_driver_target(policy, target_khz, CPUFREQ_RELATION_H);
        cpufreq_cpu_put(policy);
    }

    kfree(req);
}

/* temp boost */
int pc_request_temp_boost(unsigned int khz, unsigned int ms)
{
    struct pc_freq_request *req;
    if (!pc_wq || !ms) return -EINVAL;

    req = kzalloc(sizeof(*req), GFP_KERNEL);
    if (!req) return -ENOMEM;

    INIT_WORK(&req->work, pc_apply_work);
    req->khz = khz;
    queue_work(pc_wq, &req->work);
    return 0;
}
EXPORT_SYMBOL_GPL(pc_request_temp_boost);

/* persistent limit */
int pc_set_persistent_limit(unsigned int khz)
{
    struct pc_freq_request *req;
    if (!pc_wq) return -ENODEV;

    mutex_lock(&pc_lock);
    if (pc_cpu_limit_khz == khz) {
        mutex_unlock(&pc_lock);
        return 0;
    }
    pc_cpu_limit_khz = khz;
    mutex_unlock(&pc_lock);

    req = kzalloc(sizeof(*req), GFP_KERNEL);
    if (!req) return -ENOMEM;

    INIT_WORK(&req->work, pc_apply_work);
    req->khz = khz;
    queue_work(pc_wq, &req->work);
    pr_info("pc: persistent limit request %u kHz\n", khz);
    return 0;
}
EXPORT_SYMBOL_GPL(pc_set_persistent_limit);

/* sysfs */
static ssize_t fg_pid_show(struct kobject *k, struct kobj_attribute *attr, char *buf)
{
    ssize_t ret;
    mutex_lock(&pc_fg_lock);
    ret = sprintf(buf, "%d\n", pc_fg_pid);
    mutex_unlock(&pc_fg_lock);
    return ret;
}
static ssize_t fg_pid_store(struct kobject *k, struct kobj_attribute *attr, const char *buf, size_t count)
{
    pid_t v = 0;
    if (kstrtoint(buf, 10, &v) == 0) {
        mutex_lock(&pc_fg_lock);
        pc_fg_pid = v <= 0 ? 0 : v;
        mutex_unlock(&pc_fg_lock);
    }
    return count;
}
static struct kobj_attribute fg_pid_attr = __ATTR(fg_pid, 0644, fg_pid_show, fg_pid_store);

static ssize_t screen_show(struct kobject *k, struct kobj_attribute *attr, char *buf)
{
    return sprintf(buf, "%d\n", pc_screen_on ? 1 : 0);
}
static ssize_t screen_store(struct kobject *k, struct kobj_attribute *attr, const char *buf, size_t count)
{
    int v;
    if (kstrtoint(buf, 10, &v) == 0)
        pc_screen_on = !!v;
    return count;
}
static struct kobj_attribute screen_attr = __ATTR(screen_on, 0644, screen_show, screen_store);

static ssize_t show_perf_mode(struct kobject *k, struct kobj_attribute *a, char *buf)
{ return sprintf(buf, "%d\n", pc_perf_mode); }
static ssize_t store_perf_mode(struct kobject *k, struct kobj_attribute *a, const char *buf, size_t len)
{ int v; if (kstrtoint(buf,10,&v)) return -EINVAL; pc_perf_mode = !!v; pc_set_persistent_limit(pc_cpu_limit_khz); return len; }
static struct kobj_attribute perf_mode_attr = __ATTR(perf_mode, 0644, show_perf_mode, store_perf_mode);

static ssize_t show_cpu_limit(struct kobject *k, struct kobj_attribute *a, char *buf)
{ return sprintf(buf, "%u\n", pc_cpu_limit_khz); }
static ssize_t store_cpu_limit(struct kobject *k, struct kobj_attribute *a, const char *buf, size_t len)
{ unsigned int v; if (kstrtouint(buf,10,&v)) return -EINVAL; pc_set_persistent_limit(v); return len; }
static struct kobj_attribute cpu_limit_attr = __ATTR(cpu_max_freq_khz, 0644, show_cpu_limit, store_cpu_limit);

static ssize_t show_boost_list(struct kobject *k, struct kobj_attribute *a, char *buf)
{ return scnprintf(buf, PC_BOOST_LIST_MAX, "%s\n", pc_boost_list); }
static ssize_t store_boost_list(struct kobject *k, struct kobj_attribute *a, const char *buf, size_t len)
{ mutex_lock(&pc_lock); strlcpy(pc_boost_list, buf, sizeof(pc_boost_list)); mutex_unlock(&pc_lock); return len; }
static struct kobj_attribute boost_list_attr = __ATTR(boost_list, 0644, show_boost_list, store_boost_list);

static ssize_t show_nyako(struct kobject *k, struct kobj_attribute *a, char *buf)
{ return sprintf(buf, "%d\n", pc_nyako_enabled); }
static ssize_t store_nyako(struct kobject *k, struct kobj_attribute *a, const char *buf, size_t len)
{ int v; if (kstrtoint(buf,10,&v)) return -EINVAL; pc_nyako_enabled = !!v; return len; }
static struct kobj_attribute nyako_attr = __ATTR(nyako, 0644, show_nyako, store_nyako);

/* init / exit */
static int __init pc_init(void)
{
    int rc;
    pc_wq = create_singlethread_workqueue("pc_wq");
    if (!pc_wq) return -ENOMEM;

    pc_kobj = kobject_create_and_add("power_control", kernel_kobj);
    if (!pc_kobj) {
        destroy_workqueue(pc_wq);
        return -ENOMEM;
    }

    rc = sysfs_create_file(pc_kobj, &fg_pid_attr.attr); if (rc) goto fail;
    rc = sysfs_create_file(pc_kobj, &screen_attr.attr); if (rc) goto fail;
    rc = sysfs_create_file(pc_kobj, &perf_mode_attr.attr); if (rc) goto fail;
    rc = sysfs_create_file(pc_kobj, &cpu_limit_attr.attr); if (rc) goto fail;
    rc = sysfs_create_file(pc_kobj, &boost_list_attr.attr); if (rc) goto fail;
    rc = sysfs_create_file(pc_kobj, &nyako_attr.attr); if (rc) goto fail;

    pr_info("power_control: core online\n");
    return 0;

fail:
    kobject_put(pc_kobj);
    destroy_workqueue(pc_wq);
    return rc;
}
module_init(pc_init);

static void __exit pc_exit(void)
{
    if (pc_kobj) {
        sysfs_remove_file(pc_kobj, &fg_pid_attr.attr);
        sysfs_remove_file(pc_kobj, &screen_attr.attr);
        sysfs_remove_file(pc_kobj, &perf_mode_attr.attr);
        sysfs_remove_file(pc_kobj, &cpu_limit_attr.attr);
        sysfs_remove_file(pc_kobj, &boost_list_attr.attr);
        sysfs_remove_file(pc_kobj, &nyako_attr.attr);
        kobject_put(pc_kobj);
    }
    if (pc_wq) destroy_workqueue(pc_wq);
}
module_exit(pc_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("PowerControl Balanced (modified)");
MODULE_DESCRIPTION("Event-driven power control core with fg_pid export and 4W override");
