#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/jiffies.h>
#include <linux/kobject.h>
#include <linux/sysfs.h>
#include <linux/sched/signal.h>
#include <linux/sched.h>
#include <linux/mutex.h>
#include <linux/input.h>
#include <linux/fb.h>
#include <linux/notifier.h>
#include <linux/cpumask.h>
#include <linux/cpufreq.h>
#include <linux/slab.h>
#include <linux/workqueue.h>
#include <linux/cpu.h>
#include <linux/delay.h>
#include <linux/device.h>
#include <linux/string.h>
#include <linux/timer.h>
#include <linux/fs.h>
#include <linux/uaccess.h>
#include <linux/file.h>
#include <linux/proc_fs.h>
#include <linux/vmalloc.h>
#include <linux/list.h>
#include <linux/ctype.h>
#include <linux/namei.h>
#include <linux/mount.h>

#define LOCK_FREQ_KHZ 300000U
#define LITTLE_CORE_IDLE_FREQ_KHZ 200000U
#define LITTLE_CORE_MIN_KHZ 200000U
#define LITTLE_CORE_MAX_KHZ 1200000U
#define BIG_CORE_IDLE_FREQ_KHZ 300000U
#define BIG_CORE_MID_FREQ_KHZ 800000U
#define BIG_CORE_MAX_FREQ_KHZ 1600000U

#define LITTLE_START 0
#define LITTLE_END 3
#define BIG_START 4
#define BIG_END 7

#define SCREEN_OFF_LITTLE_CORE_0 0
#define SCREEN_OFF_LITTLE_CORE_1 1
#define SCREEN_OFF_DELAY_MS 1000
#define IDLE_NO_TOUCH_DELAY_MS 3000
#define CHECK_INTERVAL_MS 200
#define BOOST_DURATION_MS 3000

#define LOAD_THRESHOLD_LOW 30
#define LOAD_THRESHOLD_MID 50
#define LOAD_THRESHOLD_HIGH 70

#define BIG_CORE_LOAD_THRESHOLD 60
#define ALL_CORE_LOAD_THRESHOLD 75

#define POWER_BUDGET_SCREEN_OFF 700000
#define POWER_BUDGET_SCREEN_ON  2000000

#define BOOST_JSON_PATH "/data/media/0/Android/boost.json"
#define MAX_JSON_FILE_SIZE 65536
#define MAX_PACKAGE_NAME_LEN 256
#define MAX_APP_NAME_LEN 128
#define MAX_APPS_PER_CATEGORY 500

static cpumask_t little_mask;
static cpumask_t big_mask;
static cpumask_t all_mask;
static cpumask_t screen_off_mask;
static cpumask_t screen_off_active_mask;

struct fa_core_state {
    int cpu_id;
    bool active;
    unsigned int cur_freq;
    unsigned long load_val;
    struct cpufreq_policy *cpufreq_policy;
};

static struct fa_core_state fa_core_states[NR_CPUS];
static struct input_handler fa_input_handler;
static pid_t fg_pid = 0;
static bool screen_on = true;
static bool boot_complete = false;
static bool screen_off_processed = false;
static bool screen_idle_mode = false;
static bool input_handler_registered = false;
static bool module_exiting = false;
static bool cpufreq_ready = false;
static bool thermal_throttle = false;
static bool low_power_mode = false;
static DEFINE_MUTEX(fg_lock);
static unsigned long last_touch_jiffies;

static char *app_categories[3][MAX_APPS_PER_CATEGORY];
static int app_counts[3] = {0};
static DEFINE_MUTEX(category_lock);

static struct delayed_work check_work;
static struct work_struct boost_work;
static struct delayed_work screen_off_work;
static struct delayed_work boot_complete_work;
static struct delayed_work idle_check_work;
static struct delayed_work freq_adjust_work;
static struct workqueue_struct *fa_wq;

static bool is_data_mounted(void)
{
    struct path path;
    const char *fs_name;
    int ret;

    ret = kern_path("/data", LOOKUP_FOLLOW, &path);
    if (ret)
        return false;

    fs_name = path.mnt->mnt_sb->s_type->name;

    if (!strcmp(fs_name, "rootfs") || !strcmp(fs_name, "tmpfs")) {
        path_put(&path);
        return false;
    }

    path_put(&path);
    return true;
}

struct task_info {
    pid_t pid;
    char package_name[MAX_PACKAGE_NAME_LEN];
    bool is_foreground;
    bool is_boosted;
    bool is_heavy_task;
    unsigned long last_boost_jiffies;
    unsigned long last_check_jiffies;
    unsigned long avg_cpu_load;
    unsigned long power_estimate;
    struct list_head list;
};

static LIST_HEAD(task_list);
static DEFINE_SPINLOCK(task_list_lock);

struct app_category_info {
    char package_name[MAX_PACKAGE_NAME_LEN];
    char app_name[MAX_APP_NAME_LEN];
    int category;
    bool user_defined;
    struct list_head list;
};

static LIST_HEAD(app_category_list);
static DEFINE_SPINLOCK(app_category_lock);

static void init_masks(void)
{
    int i;
    cpumask_clear(&little_mask);
    for (i = LITTLE_START; i <= LITTLE_END; i++) {
        if (cpu_possible(i)) {
            cpumask_set_cpu(i, &little_mask);
        }
    }
    cpumask_clear(&big_mask);
    for (i = BIG_START; i <= BIG_END; i++) {
        if (cpu_possible(i)) {
            cpumask_set_cpu(i, &big_mask);
        }
    }
    cpumask_copy(&all_mask, cpu_possible_mask);
    cpumask_copy(&screen_off_mask, &little_mask);
    cpumask_clear(&screen_off_active_mask);
    cpumask_set_cpu(SCREEN_OFF_LITTLE_CORE_0, &screen_off_active_mask);
    cpumask_set_cpu(SCREEN_OFF_LITTLE_CORE_1, &screen_off_active_mask);
}

static void init_fa_core_states(void)
{
    int i;
    for (i = 0; i < NR_CPUS; i++) {
        fa_core_states[i].cpu_id = i;
        fa_core_states[i].active = true;
        fa_core_states[i].cur_freq = 0;
        fa_core_states[i].load_val = 0;
        fa_core_states[i].cpufreq_policy = NULL;
    }
}

static bool check_cpufreq_ready(void)
{
#ifdef CONFIG_CPU_FREQ
    static bool checked = false;
    if (checked)
        return cpufreq_ready;
    if (cpufreq_cpu_get(0) != NULL) {
        cpufreq_cpu_put(cpufreq_cpu_get(0));
        cpufreq_ready = true;
    }
    checked = true;
    return cpufreq_ready;
#else
    return false;
#endif
}

static void safe_set_cpu_freq(const cpumask_t *mask, unsigned int khz)
{
#ifdef CONFIG_CPU_FREQ
    int cpu;
    struct cpufreq_policy *policy;
    if (!check_cpufreq_ready() || module_exiting)
        return;
    for_each_cpu(cpu, mask) {
        if (!cpu_online(cpu))
            continue;
        policy = cpufreq_cpu_get(cpu);
        if (!policy)
            continue;
        if (policy->cur != khz) {
            if (policy->max >= khz && policy->min <= khz) {
                cpufreq_driver_target(policy, khz, CPUFREQ_RELATION_L);
            }
        }
        cpufreq_cpu_put(policy);
    }
#endif
}

static void safe_set_all_big_core_freq(unsigned int khz)
{
    safe_set_cpu_freq(&big_mask, khz);
}

static void safe_set_all_little_core_freq(unsigned int khz)
{
    safe_set_cpu_freq(&little_mask, khz);
}

static void deep_sleep_inactive_cores(const cpumask_t *active_mask)
{
    int cpu;
    struct cpufreq_policy *policy;
    
    if (!check_cpufreq_ready() || module_exiting)
        return;
    
    for_each_possible_cpu(cpu) {
        if (!cpumask_test_cpu(cpu, active_mask)) {
            policy = cpufreq_cpu_get(cpu);
            if (policy) {
                if (cpumask_test_cpu(cpu, &little_mask)) {
                    safe_set_cpu_freq(cpumask_of(cpu), LITTLE_CORE_IDLE_FREQ_KHZ);
                } else {
                    safe_set_cpu_freq(cpumask_of(cpu), BIG_CORE_IDLE_FREQ_KHZ);
                }
                cpufreq_cpu_put(policy);
            }
            
            if (cpu_online(cpu) && cpu > 1) {
                cpu_down(cpu);
            }
        }
    }
}

static unsigned int get_cpu_load(int cpu)
{
    unsigned long total_time = 0, idle_time = 0;
    static unsigned long prev_total[NR_CPUS] = {0};
    static unsigned long prev_idle[NR_CPUS] = {0};
    unsigned long delta_total, delta_idle;
    unsigned int load = 0;
    if (cpu < 0 || cpu >= nr_cpu_ids)
        return 0;
    total_time = jiffies_to_usecs(jiffies);
    idle_time = total_time / 2;
    if (prev_total[cpu] > 0) {
        delta_total = total_time - prev_total[cpu];
        delta_idle = idle_time - prev_idle[cpu];
        if (delta_total > 0) {
            load = 100 * (delta_total - delta_idle) / delta_total;
            if (load > 100) load = 100;
        } else {
            load = 0;
        }
    } else {
        load = 0;
    }
    prev_total[cpu] = total_time;
    prev_idle[cpu] = idle_time;
    return load;
}

static unsigned int get_big_core_load(void)
{
    int cpu;
    unsigned int total_load = 0;
    int count = 0;
    for_each_cpu(cpu, &big_mask) {
        if (cpu_online(cpu)) {
            total_load += get_cpu_load(cpu);
            count++;
        }
    }
    return count > 0 ? (total_load / count) : 0;
}

static unsigned int get_little_core_load(void)
{
    int cpu;
    unsigned int total_load = 0;
    int count = 0;
    for_each_cpu(cpu, &little_mask) {
        if (cpu_online(cpu)) {
            total_load += get_cpu_load(cpu);
            count++;
        }
    }
    return count > 0 ? (total_load / count) : 0;
}

static unsigned long estimate_power_consumption(void)
{
    unsigned long total_power = 0;
    int i;
    struct cpufreq_policy *policy;
    
    for_each_online_cpu(i) {
        unsigned int freq = 0;
        unsigned int load = get_cpu_load(i);
        
        policy = cpufreq_cpu_get(i);
        if (policy) {
            freq = policy->cur;
            cpufreq_cpu_put(policy);
        }
        
        if (freq > 0) {
            unsigned long core_power;
            if (cpumask_test_cpu(i, &big_mask)) {
                core_power = (freq / 1000000) * load * 3;
            } else {
                core_power = (freq / 1000000) * load * 1;
            }
            total_power += core_power;
        }
    }
    
    return total_power;
}

static bool get_package_name_from_pid(pid_t pid, char *buf, size_t buf_size)
{
    char cmdline_path[64];
    struct file *fp = NULL;
    loff_t pos = 0;
    char cmdline[MAX_PACKAGE_NAME_LEN];
    ssize_t len;
    char *pkg_start, *pkg_end;
    if (!buf || buf_size < 2)
        return false;
    buf[0] = '\0';
    snprintf(cmdline_path, sizeof(cmdline_path), "/proc/%d/cmdline", pid);
    fp = filp_open(cmdline_path, O_RDONLY, 0);
    if (IS_ERR(fp))
        return false;
    len = kernel_read(fp, cmdline, sizeof(cmdline) - 1, &pos);
    filp_close(fp, NULL);
    if (len <= 0)
        return false;
    cmdline[len] = '\0';
    if (cmdline[0] == '/') {
        char *last_slash = strrchr(cmdline, '/');
        if (last_slash)
            pkg_start = last_slash + 1;
        else
            pkg_start = cmdline;
    } else {
        pkg_start = cmdline;
    }
    pkg_end = strchr(pkg_start, ':');
    if (!pkg_end) {
        pkg_end = pkg_start + strlen(pkg_start);
    }
    if (pkg_end > pkg_start && strchr(pkg_start, '.')) {
        size_t pkg_len = pkg_end - pkg_start;
        if (pkg_len > 0 && pkg_len < buf_size) {
            strncpy(buf, pkg_start, pkg_len);
            buf[pkg_len] = '\0';
            return true;
        }
    }
    return false;
}

static struct task_info *find_task_info(pid_t pid)
{
    struct task_info *info;
    spin_lock(&task_list_lock);
    list_for_each_entry(info, &task_list, list) {
        if (info->pid == pid) {
            spin_unlock(&task_list_lock);
            return info;
        }
    }
    spin_unlock(&task_list_lock);
    return NULL;
}

static void update_task_info(struct task_struct *task)
{
    struct task_info *info;
    char package_name[MAX_PACKAGE_NAME_LEN];
    bool is_foreground = (task->pid == fg_pid);
    unsigned int freq = 0;
    if (!task->mm)
        return;
    if (!get_package_name_from_pid(task->pid, package_name, sizeof(package_name))) {
        return;
    }
    info = find_task_info(task->pid);
    if (!info) {
        info = kzalloc(sizeof(*info), GFP_ATOMIC);
        if (!info)
            return;
        info->pid = task->pid;
        strncpy(info->package_name, package_name, sizeof(info->package_name) - 1);
        info->package_name[sizeof(info->package_name) - 1] = '\0';
        info->is_foreground = is_foreground;
        info->is_boosted = false;
        info->is_heavy_task = false;
        info->last_boost_jiffies = 0;
        info->last_check_jiffies = jiffies;
        info->avg_cpu_load = 0;
        info->power_estimate = 0;
        spin_lock(&task_list_lock);
        list_add_tail(&info->list, &task_list);
        spin_unlock(&task_list_lock);
    } else {
        info->is_foreground = is_foreground;
        if (is_foreground) {
            info->last_check_jiffies = jiffies;
        }
        info->avg_cpu_load = (info->avg_cpu_load * 7 + get_cpu_load(task_cpu(task))) / 8;
#ifdef CONFIG_CPU_FREQ
        {
            struct cpufreq_policy *policy = cpufreq_cpu_get(task_cpu(task));
            if (policy) {
                freq = policy->cur;
                cpufreq_cpu_put(policy);
            }
        }
#endif
        if (freq > 0) {
            unsigned int load = get_cpu_load(task_cpu(task));
            unsigned long cpu_power = (freq / 1000000) * load * 2;
            info->power_estimate = (info->power_estimate * 7 + cpu_power * 100) / 8;
            if (load > LOAD_THRESHOLD_HIGH && cpu_power > 1000) {
                info->is_heavy_task = true;
            } else if (load < LOAD_THRESHOLD_LOW && cpu_power < 500) {
                info->is_heavy_task = false;
            }
        }
    }
}

static int get_app_category_from_config(const char *package_name)
{
    int i;
    if (!package_name)
        return 0;
    mutex_lock(&category_lock);
    for (i = 0; i < app_counts[2]; i++) {
        if (app_categories[2][i] && strcmp(package_name, app_categories[2][i]) == 0) {
            mutex_unlock(&category_lock);
            return 2;
        }
    }
    for (i = 0; i < app_counts[1]; i++) {
        if (app_categories[1][i] && strcmp(package_name, app_categories[1][i]) == 0) {
            mutex_unlock(&category_lock);
            return 1;
        }
    }
    for (i = 0; i < app_counts[0]; i++) {
        if (app_categories[0][i] && strcmp(package_name, app_categories[0][i]) == 0) {
            mutex_unlock(&category_lock);
            return 0;
        }
    }
    mutex_unlock(&category_lock);
    return -1;
}

static void apply_scheduling_policy(struct task_struct *task, struct task_info *info)
{
    int category = get_app_category_from_config(info->package_name);
    unsigned int big_load = get_big_core_load();
    unsigned int little_load = get_little_core_load();
    if (category == 2) {
        set_user_nice(task, -20);
        set_cpus_allowed_ptr(task, &all_mask);
        if (check_cpufreq_ready() && !thermal_throttle && !low_power_mode) {
            safe_set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
            safe_set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        }
    } else if (category == 1) {
        if (big_load < BIG_CORE_LOAD_THRESHOLD) {
            set_user_nice(task, -10);
            set_cpus_allowed_ptr(task, &big_mask);
        } else {
            set_user_nice(task, 0);
            set_cpus_allowed_ptr(task, &all_mask);
        }
    } else {
        if (info->is_heavy_task && big_load < BIG_CORE_LOAD_THRESHOLD) {
            set_user_nice(task, -5);
            set_cpus_allowed_ptr(task, &big_mask);
        } else {
            set_user_nice(task, 5);
            set_cpus_allowed_ptr(task, &little_mask);
            if (little_load > LOAD_THRESHOLD_HIGH && big_load < BIG_CORE_LOAD_THRESHOLD) {
                set_user_nice(task, 0);
                set_cpus_allowed_ptr(task, &all_mask);
            }
        }
    }
}

static void enhanced_task_scheduler(void)
{
    struct task_struct *p;
    struct task_info *info;
    if (!screen_on || screen_idle_mode || screen_off_processed || module_exiting)
        return;
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        if (p->pid <= 100)
            continue;
        update_task_info(p);
        info = find_task_info(p->pid);
        if (!info)
            continue;
        apply_scheduling_policy(p, info);
    }
    rcu_read_unlock();
}

static void screen_off_scheduling_policy(void)
{
    struct task_struct *p;
    
    if (screen_on || !screen_off_processed)
        return;
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        if (p->pid > 100) {
            set_cpus_allowed_ptr(p, &screen_off_active_mask);
            set_user_nice(p, 19);
        }
        
        if (p->pid <= 100) {
            set_cpus_allowed_ptr(p, cpumask_of(SCREEN_OFF_LITTLE_CORE_0));
        }
    }
    rcu_read_unlock();
    
    safe_set_cpu_freq(&screen_off_active_mask, LITTLE_CORE_IDLE_FREQ_KHZ);
    deep_sleep_inactive_cores(&screen_off_active_mask);
}

static void adjust_frequencies_with_power_budget(void)
{
    unsigned int big_load = get_big_core_load();
    unsigned int little_load = get_little_core_load();
    unsigned long current_power = estimate_power_consumption();
    unsigned long power_budget = screen_on ? POWER_BUDGET_SCREEN_ON : POWER_BUDGET_SCREEN_OFF;
    
    if (!screen_on || !check_cpufreq_ready() || thermal_throttle)
        return;
    
    if (screen_idle_mode || screen_off_processed) {
        safe_set_all_little_core_freq(LITTLE_CORE_IDLE_FREQ_KHZ);
        safe_set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        return;
    }
    
    if (current_power > power_budget) {
        if (big_load > 50) {
            safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
        } else {
            safe_set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        }
        
        if (little_load > 60) {
            safe_set_all_little_core_freq((LITTLE_CORE_MIN_KHZ + LITTLE_CORE_MAX_KHZ) / 3);
        } else {
            safe_set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        }
        return;
    }
    
    if (low_power_mode) {
        safe_set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        safe_set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        return;
    }
    
    if (little_load < LOAD_THRESHOLD_LOW) {
        safe_set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    } else if (little_load < LOAD_THRESHOLD_MID) {
        safe_set_all_little_core_freq((LITTLE_CORE_MIN_KHZ + LITTLE_CORE_MAX_KHZ) / 4);
    } else if (little_load < LOAD_THRESHOLD_HIGH) {
        safe_set_all_little_core_freq((LITTLE_CORE_MIN_KHZ + LITTLE_CORE_MAX_KHZ) / 2);
    } else {
        safe_set_all_little_core_freq(LITTLE_CORE_MAX_KHZ * 3 / 4);
    }
    
    if (big_load < LOAD_THRESHOLD_LOW) {
        safe_set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    } else if (big_load < LOAD_THRESHOLD_MID) {
        safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ * 2 / 3);
    } else if (big_load < LOAD_THRESHOLD_HIGH) {
        safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
    } else {
        safe_set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ * 3 / 4);
    }
}

static void enter_screen_idle_mode(void)
{
    if (!screen_on || screen_idle_mode || screen_off_processed || !check_cpufreq_ready())
        return;
    screen_idle_mode = true;
    safe_set_all_little_core_freq(LOCK_FREQ_KHZ);
    safe_set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
}

static void exit_screen_idle_mode(void)
{
    if (!screen_idle_mode || !check_cpufreq_ready())
        return;
    screen_idle_mode = false;
    safe_set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
}

static void schedule_screen_off_mode(void)
{
    struct task_struct *p;
    int cpu;
    cpumask_t big_only, little_inactive;
    
    if (screen_off_processed)
        return;
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        if (p->pid > 100) {
            set_user_nice(p, 19);
            set_cpus_allowed_ptr(p, &little_mask);
        }
    }
    rcu_read_unlock();
    
    msleep(50);
    screen_off_scheduling_policy();
    safe_set_all_little_core_freq(LITTLE_CORE_IDLE_FREQ_KHZ);
    
    cpumask_andnot(&big_only, &big_mask, &screen_off_active_mask);
    for_each_cpu(cpu, &big_only) {
        if (cpu_online(cpu)) {
            cpu_down(cpu);
        }
    }
    
    cpumask_andnot(&little_inactive, &little_mask, &screen_off_active_mask);
    for_each_cpu(cpu, &little_inactive) {
        if (cpu_online(cpu) && cpu > SCREEN_OFF_LITTLE_CORE_1) {
            cpu_down(cpu);
        }
    }
    
    screen_off_processed = true;
    screen_idle_mode = false;
}

static void schedule_screen_on_mode(void)
{
    struct task_struct *p;
    int cpu;
    
    for_each_possible_cpu(cpu) {
        if (!cpu_online(cpu)) {
            cpu_up(cpu);
        }
    }
    
    safe_set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        if (p->pid > 100) {
            set_user_nice(p, 0);
            set_cpus_allowed_ptr(p, &all_mask);
        }
    }
    rcu_read_unlock();
    
    screen_off_processed = false;
    screen_idle_mode = false;
    
    if (fa_wq && !module_exiting) {
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &idle_check_work, msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        queue_delayed_work(fa_wq, &freq_adjust_work, msecs_to_jiffies(1000));
    }
}

static void check_work_func(struct work_struct *work)
{
    struct task_info *info, *tmp;
    struct task_struct *task;
    
    if (module_exiting || !fa_wq || !boot_complete)
        return;
    
    if (screen_on && !screen_off_processed) {
        enhanced_task_scheduler();
    }
    
    adjust_frequencies_with_power_budget();
    
    spin_lock(&task_list_lock);
    list_for_each_entry_safe(info, tmp, &task_list, list) {
        if (time_after(jiffies, info->last_check_jiffies + msecs_to_jiffies(60000))) {
            rcu_read_lock();
            task = find_task_by_vpid(info->pid);
            if (!task) {
                list_del(&info->list);
                kfree(info);
            }
            rcu_read_unlock();
        }
    }
    spin_unlock(&task_list_lock);
    
    if (fa_wq && !module_exiting && boot_complete && screen_on && !screen_off_processed) {
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
    }
}

static void boost_work_func(struct work_struct *work)
{
    struct task_info *info;
    int category;
    if (module_exiting || fg_pid == 0 || !check_cpufreq_ready() || !boot_complete)
        return;
    if (screen_idle_mode) {
        exit_screen_idle_mode();
    }
    info = find_task_info(fg_pid);
    if (info) {
        info->last_boost_jiffies = jiffies;
        info->is_boosted = true;
        category = get_app_category_from_config(info->package_name);
        if (category == 2) {
            safe_set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
            safe_set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        } else if (category == 1) {
            safe_set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
            safe_set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        } else {
            safe_set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
            safe_set_all_little_core_freq((LITTLE_CORE_MIN_KHZ + LITTLE_CORE_MAX_KHZ) / 2);
        }
    }
}

static void idle_check_work_func(struct work_struct *work)
{
    unsigned long now = jiffies;
    unsigned long idle_timeout = msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS);
    if (module_exiting || !screen_on || screen_idle_mode || screen_off_processed)
        return;
    if (time_after(now, last_touch_jiffies + idle_timeout)) {
        enter_screen_idle_mode();
    } else {
        if (fa_wq && !module_exiting) {
            queue_delayed_work(fa_wq, &idle_check_work, msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        }
    }
}

static void freq_adjust_work_func(struct work_struct *work)
{
    if (module_exiting || !fa_wq || !boot_complete)
        return;
    adjust_frequencies_with_power_budget();
    if (fa_wq && !module_exiting && boot_complete && screen_on && !screen_off_processed) {
        queue_delayed_work(fa_wq, &freq_adjust_work, msecs_to_jiffies(1000));
    }
}

static void free_categories(void)
{
    int i, j;
    mutex_lock(&category_lock);
    for (i = 0; i < 3; i++) {
        for (j = 0; j < app_counts[i]; j++) {
            if (app_categories[i][j]) {
                kfree(app_categories[i][j]);
                app_categories[i][j] = NULL;
            }
        }
        app_counts[i] = 0;
    }
    mutex_unlock(&category_lock);
}

static void load_boost_config(void)
{
    struct file *fp;
    loff_t pos = 0;
    char *buf;
    char *p;
    char *str;
    int current_category = -1;
    bool expect_category = false;
    int idx[3] = {0, 0, 0};

    printk(KERN_ERR "FA: load_boost_config enter\n");

    if (!is_data_mounted()) {
        printk(KERN_ERR "FA: /data not mounted, abort load\n");
        return;
    }

    printk(KERN_ERR "FA: /data mounted, continue\n");

    free_categories();

    fp = filp_open(BOOST_JSON_PATH, O_RDONLY, 0);
    if (IS_ERR(fp)) {
        printk(KERN_ERR "FA: open failed path=%s err=%ld\n",
               BOOST_JSON_PATH, PTR_ERR(fp));
        return;
    }

    printk(KERN_ERR "FA: open success path=%s\n", BOOST_JSON_PATH);

    buf = kzalloc(MAX_JSON_FILE_SIZE, GFP_KERNEL);
    if (!buf) {
        printk(KERN_ERR "FA: kzalloc failed size=%d\n", MAX_JSON_FILE_SIZE);
        filp_close(fp, NULL);
        return;
    }

    kernel_read(fp, buf, MAX_JSON_FILE_SIZE - 1, &pos);
    filp_close(fp, NULL);

    printk(KERN_ERR "FA: file read done bytes=%lld\n", pos);

    mutex_lock(&category_lock);

    p = buf;
    while (*p) {

        if (*p == '[') {
            expect_category = true;
            current_category = -1;
            p++;
            continue;
        }

        if (*p == ']') {
            printk(KERN_ERR "FA: category end c0=%d c1=%d c2=%d\n",
                   idx[0], idx[1], idx[2]);
            current_category = -1;
            expect_category = false;
            p++;
            continue;
        }

        if (*p != '"') {
            p++;
            continue;
        }

        str = ++p;
        while (*p && *p != '"')
            p++;

        if (*p != '"')
            break;

        *p = '\0';

        if (expect_category) {
            if (!strcmp(str, "0-3")) {
                current_category = 0;
                printk(KERN_ERR "FA: category switch -> 0-3\n");
            } else if (!strcmp(str, "4-7")) {
                current_category = 1;
                printk(KERN_ERR "FA: category switch -> 4-7\n");
            } else if (!strcmp(str, "0-7")) {
                current_category = 2;
                printk(KERN_ERR "FA: category switch -> 0-7\n");
            } else {
                current_category = -1;
                printk(KERN_ERR "FA: unknown category %s\n", str);
            }
            expect_category = false;
        } else if (current_category >= 0 &&
                   idx[current_category] < MAX_APPS_PER_CATEGORY) {

            size_t len = strlen(str);
            if (len > 0 && len < MAX_PACKAGE_NAME_LEN) {
                app_categories[current_category][idx[current_category]] =
                    kzalloc(len + 1, GFP_KERNEL);
                if (app_categories[current_category][idx[current_category]]) {
                    strcpy(app_categories[current_category][idx[current_category]], str);
                    printk(KERN_ERR "FA: add app c=%d idx=%d pkg=%s\n",
                           current_category,
                           idx[current_category],
                           app_categories[current_category][idx[current_category]]);
                    idx[current_category]++;
                    app_counts[current_category] = idx[current_category];
                } else {
                    printk(KERN_ERR "FA: alloc app failed c=%d pkg=%s\n",
                           current_category, str);
                }
            } else {
                printk(KERN_ERR "FA: invalid pkg len=%zu name=%s\n", len, str);
            }
        }

        p++;
    }

    mutex_unlock(&category_lock);
    kfree(buf);

    printk(KERN_ERR "FA: load_boost_config done total c0=%d c1=%d c2=%d\n",
           app_counts[0], app_counts[1], app_counts[2]);
}

static ssize_t save_boost_config(void)
{
    struct file *fp = NULL;
    loff_t pos = 0;
    char *json = NULL;
    int json_size = MAX_JSON_FILE_SIZE;
    int len = 0;
    int i;
    json = kzalloc(json_size, GFP_KERNEL);
    if (!json)
        return -ENOMEM;
    len += snprintf(json + len, json_size - len, "[\n");
    mutex_lock(&category_lock);
    if (app_counts[0] > 0) {
        len += snprintf(json + len, json_size - len, "    [\"0-3\",\n");
        for (i = 0; i < app_counts[0]; i++) {
            if (app_categories[0][i]) {
                len += snprintf(json + len, json_size - len, "        \"%s\",\n", app_categories[0][i]);
            }
        }
        if (len > 0 && json[len-2] == ',') {
            json[len-2] = '\n';
            json[len-1] = '\0';
            len--;
        }
        len += snprintf(json + len, json_size - len, "    ],\n");
    }
    if (app_counts[1] > 0) {
        len += snprintf(json + len, json_size - len, "    [\"4-7\",\n");
        for (i = 0; i < app_counts[1]; i++) {
            if (app_categories[1][i]) {
                len += snprintf(json + len, json_size - len, "        \"%s\",\n", app_categories[1][i]);
            }
        }
        if (len > 0 && json[len-2] == ',') {
            json[len-2] = '\n';
            json[len-1] = '\0';
            len--;
        }
        len += snprintf(json + len, json_size - len, "    ],\n");
    }
    if (app_counts[2] > 0) {
        len += snprintf(json + len, json_size - len, "    [\"0-7\",\n");
        for (i = 0; i < app_counts[2]; i++) {
            if (app_categories[2][i]) {
                len += snprintf(json + len, json_size - len, "        \"%s\",\n", app_categories[2][i]);
            }
        }
        if (len > 0 && json[len-2] == ',') {
            json[len-2] = '\n';
            json[len-1] = '\0';
            len--;
        }
        len += snprintf(json + len, json_size - len, "    ]\n");
    }
    mutex_unlock(&category_lock);
    len += snprintf(json + len, json_size - len, "]\n");
    fp = filp_open(BOOST_JSON_PATH, O_CREAT | O_WRONLY | O_TRUNC, 0644);
    if (IS_ERR(fp)) {
        kfree(json);
        return PTR_ERR(fp);
    }
    kernel_write(fp, json, len, &pos);
    filp_close(fp, NULL);
    kfree(json);
    return 0;
}

static void scan_installed_apps(void)
{
    struct app_category_info *info;
    struct file *fp = NULL;
    char dir_name[256];
    char *dash;
    
    fp = filp_open("/data/app", O_RDONLY | O_DIRECTORY, 0);
    if (!IS_ERR(fp)) {
        struct dentry *dentry = fp->f_path.dentry;
        if (dentry && dentry->d_inode) {
            struct dentry *child;
            struct list_head *pos;
            list_for_each(pos, &dentry->d_subdirs) {
                child = list_entry(pos, struct dentry, d_child);
                if (child && child->d_inode && S_ISDIR(child->d_inode->i_mode)) {
                    strncpy(dir_name, child->d_name.name, sizeof(dir_name)-1);
                    dir_name[sizeof(dir_name)-1] = '\0';
                    dash = strstr(dir_name, "-");
                    if (dash) {
                        *dash = '\0';
                        info = kzalloc(sizeof(*info), GFP_KERNEL);
                        if (info) {
                            strncpy(info->package_name, dir_name, sizeof(info->package_name)-1);
                            info->package_name[sizeof(info->package_name)-1] = '\0';
                            strncpy(info->app_name, dir_name, sizeof(info->app_name)-1);
                            info->app_name[sizeof(info->app_name)-1] = '\0';
                            info->category = 0;
                            info->user_defined = false;
                            spin_lock(&app_category_lock);
                            list_add_tail(&info->list, &app_category_list);
                            spin_unlock(&app_category_lock);
                        }
                    }
                }
            }
        }
        filp_close(fp, NULL);
    }
}

static void boot_complete_work_func(struct work_struct *work)
{
    boot_complete = true;
    load_boost_config();
    scan_installed_apps();
    msleep(2000);
    if (!input_handler_registered && fa_wq && !module_exiting) {
        int rc = input_register_handler(&fa_input_handler);
        if (rc == 0) {
            input_handler_registered = true;
        }
    }
    if (screen_on && fa_wq && !module_exiting) {
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &idle_check_work, msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        queue_delayed_work(fa_wq, &freq_adjust_work, msecs_to_jiffies(1000));
    }
}

static void screen_off_work_func(struct work_struct *work)
{
    if (!screen_on && !screen_off_processed) {
        schedule_screen_off_mode();
    }
}

static int fa_input_connect(struct input_handler *handler,
                            struct input_dev *dev,
                            const struct input_device_id *id)
{
    struct input_handle *h;
    int err;
    if (!dev)
        return -ENODEV;
    h = kzalloc(sizeof(*h), GFP_KERNEL);
    if (!h)
        return -ENOMEM;
    h->dev = dev;
    h->handler = handler;
    h->name = "fair_scheduler_input";
    err = input_register_handle(h);
    if (err) {
        kfree(h);
        return err;
    }
    err = input_open_device(h);
    if (err) {
        input_unregister_handle(h);
        kfree(h);
        return err;
    }
    return 0;
}

static void fa_input_disconnect(struct input_handle *handle)
{
    if (!handle)
        return;
    input_close_device(handle);
    input_unregister_handle(handle);
    kfree(handle);
}

static void fa_input_event(struct input_handle *handle,
                           unsigned int type, unsigned int code, int value)
{
    struct task_info *info;
    if (module_exiting || !screen_on || !fa_wq || !boot_complete)
        return;
    if (type == EV_ABS || type == EV_KEY || type == EV_SYN) {
        last_touch_jiffies = jiffies;
        if (screen_idle_mode) {
            screen_idle_mode = false;
            exit_screen_idle_mode();
        }
        if (!work_pending(&boost_work) && !module_exiting)
            queue_work(fa_wq, &boost_work);
        if (!delayed_work_pending(&check_work) && !module_exiting)
            mod_delayed_work(fa_wq, &check_work, msecs_to_jiffies(50));
        if (!delayed_work_pending(&idle_check_work) && !module_exiting) {
            cancel_delayed_work(&idle_check_work);
            queue_delayed_work(fa_wq, &idle_check_work,
                             msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        }
        info = find_task_info(fg_pid);
        if (info) {
            info->last_boost_jiffies = jiffies;
        }
    }
}

static int fb_notif_call(struct notifier_block *nb,
                         unsigned long event, void *data)
{
    int *blankp;
    struct fb_event *evdata = data;
    if (event != FB_EVENT_BLANK)
        return NOTIFY_DONE;
    if (!evdata || !evdata->data)
        return NOTIFY_DONE;
    blankp = evdata->data;
    if (*blankp == FB_BLANK_UNBLANK) {
        if (!screen_on) {
            screen_on = true;
            screen_off_processed = false;
            last_touch_jiffies = jiffies;
            cancel_delayed_work(&screen_off_work);
            schedule_screen_on_mode();
            if (fa_wq && !module_exiting) {
                queue_work(fa_wq, &boost_work);
            }
        }
    } else {
        if (screen_on) {
            screen_on = false;
            cancel_delayed_work(&check_work);
            cancel_delayed_work(&idle_check_work);
            cancel_delayed_work(&freq_adjust_work);
            cancel_delayed_work(&screen_off_work);
            if (fa_wq && !module_exiting) {
                queue_delayed_work(fa_wq, &screen_off_work,
                                  msecs_to_jiffies(SCREEN_OFF_DELAY_MS));
            }
        }
    }
    return NOTIFY_OK;
}

static const struct input_device_id fa_ids[] = {
    { .driver_info = 1 },
    { }
};

static struct input_handler fa_input_handler = {
    .event = fa_input_event,
    .connect = fa_input_connect,
    .disconnect = fa_input_disconnect,
    .name = "fair_scheduler",
    .id_table = fa_ids,
};

static struct notifier_block fb_notifier = {
    .notifier_call = fb_notif_call,
};

static int __init fair_scheduler_init(void)
{
    printk(KERN_ERR "FA: fair_scheduler_init reached\n");
    init_masks();
    init_fa_core_states();
    spin_lock_init(&task_list_lock);
    spin_lock_init(&app_category_lock);
    module_exiting = false;
    boot_complete = false;
    screen_on = true;
    last_touch_jiffies = jiffies;
    fa_wq = alloc_workqueue("fair_scheduler_wq",
                           WQ_FREEZABLE | WQ_MEM_RECLAIM | WQ_UNBOUND, 1);
    if (!fa_wq) {
        printk(KERN_ERR "FA: Failed to create workqueue\n");
        return -ENOMEM;
    }
    INIT_DELAYED_WORK(&check_work, check_work_func);
    INIT_DELAYED_WORK(&screen_off_work, screen_off_work_func);
    INIT_WORK(&boost_work, boost_work_func);
    INIT_DELAYED_WORK(&boot_complete_work, boot_complete_work_func);
    INIT_DELAYED_WORK(&idle_check_work, idle_check_work_func);
    INIT_DELAYED_WORK(&freq_adjust_work, freq_adjust_work_func);
    fb_register_client(&fb_notifier);
    if (fa_wq) {
        queue_delayed_work(fa_wq, &boot_complete_work, msecs_to_jiffies(5000));
    }
    printk(KERN_INFO "Fair Scheduler Initialized Successfully\n");
    return 0;
}

static void __exit fair_scheduler_exit(void)
{
    struct task_info *info, *tmp;
    struct app_category_info *app, *atmp;
    int i, j;
    printk(KERN_INFO "Fair Scheduler Exiting\n");
    module_exiting = true;
    cancel_delayed_work_sync(&check_work);
    cancel_delayed_work_sync(&screen_off_work);
    cancel_work_sync(&boost_work);
    cancel_delayed_work_sync(&boot_complete_work);
    cancel_delayed_work_sync(&idle_check_work);
    cancel_delayed_work_sync(&freq_adjust_work);
    if (fa_wq) {
        flush_workqueue(fa_wq);
        destroy_workqueue(fa_wq);
        fa_wq = NULL;
    }
    spin_lock(&task_list_lock);
    list_for_each_entry_safe(info, tmp, &task_list, list) {
        list_del(&info->list);
        kfree(info);
    }
    spin_unlock(&task_list_lock);
    spin_lock(&app_category_lock);
    list_for_each_entry_safe(app, atmp, &app_category_list, list) {
        list_del(&app->list);
        kfree(app);
    }
    spin_unlock(&app_category_lock);
    save_boost_config();
    mutex_lock(&category_lock);
    for (i = 0; i < 3; i++) {
        for (j = 0; j < app_counts[i]; j++) {
            if (app_categories[i][j]) {
                kfree(app_categories[i][j]);
                app_categories[i][j] = NULL;
            }
        }
        app_counts[i] = 0;
    }
    mutex_unlock(&category_lock);
    if (input_handler_registered) {
        input_unregister_handler(&fa_input_handler);
        input_handler_registered = false;
    }
    fb_unregister_client(&fb_notifier);
    printk(KERN_INFO "Fair Scheduler Exited\n");
}

module_init(fair_scheduler_init);
module_exit(fair_scheduler_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Fair Scheduler");
MODULE_DESCRIPTION("Android Task Scheduler");
