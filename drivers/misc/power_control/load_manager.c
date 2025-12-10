// SPDX-License-Identifier: GPL-2.0
/*
 * load_manager.c - Event-driven energy-first strategy
 *
 * Features:
 *  - Front-app gets big cores + low nice
 *  - Background tasks moved to little cores + higher nice
 *  - Lock screen: only selected CPUs, mid-frequency
 *  - No polling / no kthread
 */

#include <linux/module.h>
#include <linux/sched/signal.h>
#include <linux/sched.h>
#include <linux/cpumask.h>
#include <linux/mutex.h>
#include <linux/workqueue.h>
#include <linux/notifier.h>
#include <linux/fb.h>
#include <linux/errno.h>

extern pid_t pc_get_fg_pid(void);
extern bool pc_is_screen_on(void);
extern int pc_request_temp_boost(unsigned int khz, unsigned int ms);
extern int pc_set_persistent_limit(unsigned int khz);

/* CPU layout - adapt to your SoC */
#define CPU_LITTLE_START 0
#define CPU_LITTLE_END   3
#define CPU_BIG_START    4
#define CPU_BIG_END      7
#define CPU_LOCK_0       5
#define CPU_LOCK_1       6

#define TEMP_BOOST_KHZ  900000
#define TEMP_BOOST_MS   120

/* background nice */
#define BG_NICE_BOOST   10

/* state */
static DEFINE_MUTEX(lm_lock);
static struct workqueue_struct *lm_wq;

/* helper: cpumask from range */
static void cpumask_range(cpumask_t *m, int a, int b)
{
    cpumask_clear(m);
    for ( ; a <= b; a++) if (cpu_online(a)) cpumask_set_cpu(a, m);
}

/* promote foreground */
static void promote_foreground(struct work_struct *work)
{
    pid_t fg = pc_get_fg_pid();
    struct task_struct *t;
    cpumask_t big_mask;
    cpumask_range(&big_mask, CPU_BIG_START, CPU_BIG_END);

    if (!fg) return;

    rcu_read_lock();
    t = find_task_by_vpid(fg);
    if (t && pid_alive(t)) {
        set_user_nice(t, -8);
        set_cpus_allowed_ptr(t, &big_mask);
        pc_request_temp_boost(TEMP_BOOST_KHZ, TEMP_BOOST_MS);
    }
    rcu_read_unlock();
}

/* demote background */
static void demote_background(struct work_struct *work)
{
    pid_t fg = pc_get_fg_pid();
    struct task_struct *p;
    cpumask_t little_mask;
    cpumask_range(&little_mask, CPU_LITTLE_START, CPU_LITTLE_END);

    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm) continue;
        if (!pid_alive(p)) continue;
        if (p->pid == fg) continue;

        set_cpus_allowed_ptr(p, &little_mask);
        set_user_nice(p, task_nice(p) + BG_NICE_BOOST);
    }
    rcu_read_unlock();
}

/* lockscreen policy */
static void apply_lockscreen_policy(struct work_struct *work)
{
    cpumask_t m;
    cpumask_clear(&m);
    if (cpu_online(CPU_LOCK_0)) cpumask_set_cpu(CPU_LOCK_0, &m);
    if (cpu_online(CPU_LOCK_1)) cpumask_set_cpu(CPU_LOCK_1, &m);

    pc_set_persistent_limit(600000); /* mid freq */
}

/* restore normal policy */
static void restore_normal_policy(struct work_struct *work)
{
    pc_set_persistent_limit(0);
}

/* work items */
static DECLARE_WORK(fg_promote_work, promote_foreground);
static DECLARE_WORK(bg_demote_work, demote_background);
static DECLARE_WORK(lockscreen_work, apply_lockscreen_policy);
static DECLARE_WORK(restore_work, restore_normal_policy);

/* fb notifier */
static int lm_fb_notif_cb(struct notifier_block *nb, unsigned long event, void *data)
{
    int *blank = data ? *(int **)(&data) : NULL;
    if (!blank) return NOTIFY_DONE;

    if (*blank == FB_BLANK_UNBLANK || *blank == FB_BLANK_NORMAL) {
        /* screen on */
        if (lm_wq) queue_work(lm_wq, &restore_work);
        if (lm_wq) {
            queue_work(lm_wq, &fg_promote_work);
            queue_work(lm_wq, &bg_demote_work);
        }
    } else {
        /* screen off */
        if (lm_wq) queue_work(lm_wq, &lockscreen_work);
    }
    return NOTIFY_OK;
}
static struct notifier_block lm_fb_notif = { .notifier_call = lm_fb_notif_cb };

/* sysfs handler for fg_pid changes */
static ssize_t fg_pid_store(struct kobject *k, struct kobj_attribute *attr,
                            const char *buf, size_t count)
{
    pid_t v;
    if (!kstrtoint(buf, 10, &v)) return count;
    v = v <= 0 ? 0 : v;

    if (lm_wq) {
        queue_work(lm_wq, &fg_promote_work);
        queue_work(lm_wq, &bg_demote_work);
    }

    return count;
}

/* init / exit */
static int __init lm_init(void)
{
    lm_wq = create_singlethread_workqueue("lm_wq");
    if (!lm_wq) return -ENOMEM;

    fb_register_client(&lm_fb_notif);
    pr_info("load_manager: event-driven policy started\n");
    return 0;
}
module_init(lm_init);

static void __exit lm_exit(void)
{
    if (lm_wq) destroy_workqueue(lm_wq);
    fb_unregister_client(&lm_fb_notif);
    pr_info("load_manager: stopped\n");
}
module_exit(lm_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("LoadManager Balanced Energy-First");
MODULE_DESCRIPTION("Event-driven foreground priority + background demotion");
