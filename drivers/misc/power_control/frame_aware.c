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
#include <linux/path.h>
#include <linux/proc_fs.h>
#include <linux/thermal.h>
#include <linux/power_supply.h>

extern int pc_set_persistent_limit(unsigned int khz);

#define LOCK_FREQ_KHZ           300000
#define BIG_CORE_IDLE_FREQ_KHZ  500000
#define BIG_CORE_MID_FREQ_KHZ   900000
#define BIG_CORE_BOOST_HZ_KHZ   1500000
#define BIG_CORE_MAX_FREQ_KHZ   2000000
#define LITTLE_CORE_MIN_KHZ     600000
#define LITTLE_CORE_MAX_KHZ     1400000
#define LITTLE_CORE_BOOST_KHZ   1800000

#define LITTLE_START 0
#define LITTLE_END   3
#define BIG_START    4
#define BIG_END      7

#define BOOST_DURATION_MS       3000
#define SCREEN_OFF_DELAY_MS     2000
#define CHECK_INTERVAL_MS       100
#define POWER_CHECK_INTERVAL_MS 500
#define MAX_TASK_CHECK          50

#define LOAD_THRESHOLD_LOW      30
#define LOAD_THRESHOLD_MID      60
#define LOAD_THRESHOLD_HIGH     80

#define POWER_THRESHOLD_LOW     3000
#define POWER_THRESHOLD_MID     4000
#define POWER_THRESHOLD_HIGH    5000
#define POWER_THRESHOLD_CRITICAL 7000

#define THERMAL_THRESHOLD       80
#define BIG_CORE_LOAD_THRESHOLD 80
#define ALL_CORE_LOAD_THRESHOLD 80

#define WHITELIST_FILE_PATH     "/data/media/0/Android/boost_whitelist.json"
#define MAX_WHITELIST_APPS      100
#define MAX_PACKAGE_NAME_LEN    256
#define MAX_CMD_LINE_LEN        512

static cpumask_t little_mask;
static cpumask_t big_mask;
static cpumask_t all_mask;
static cpumask_t screen_off_mask;

static pid_t fg_pid = 0;
static bool screen_on = true;
static bool boot_complete = false;
static bool screen_off_processed = false;
static bool power_emergency_mode = false;
static bool thermal_throttle_mode = false;
static bool full_power_mode = false;
static DEFINE_MUTEX(fg_lock);
static unsigned long last_touch_jiffies;
static unsigned long screen_off_jiffies;
static unsigned long power_check_jiffies;
static unsigned long thermal_check_jiffies;
static struct kobject *fa_kobj;

static unsigned long last_power_uw = 0;
static unsigned long avg_power_uw = 0;
static unsigned long max_power_uw = 0;
static unsigned long power_samples[10];
static int power_sample_index = 0;
static int power_sample_count = 0;

static int last_temperature = 0;

static char **app_whitelist = NULL;
static int whitelist_count = 0;
static DEFINE_MUTEX(whitelist_lock);

static struct delayed_work check_work;
static struct work_struct boost_work;
static struct delayed_work screen_off_work;
static struct delayed_work boot_complete_work;
static struct delayed_work power_check_work;
static struct delayed_work thermal_check_work;
static struct work_struct full_power_work;
static struct workqueue_struct *fa_wq;

struct task_info {
    pid_t pid;
    char package_name[MAX_PACKAGE_NAME_LEN];
    bool is_foreground;
    bool is_whitelisted;
    bool is_notification;
    bool is_heavy_task;
    unsigned long last_boost_jiffies;
    unsigned long last_power_check;
    unsigned long avg_power_uw;
    struct list_head list;
};

static LIST_HEAD(task_list);
static DEFINE_SPINLOCK(task_list_lock);

static const char *default_notification_apps[] = {
    "com.android.systemui",
    "com.android.phone",
    "com.android.mms",
    "com.android.providers.telephony",
    "com.android.dialer",
    "com.android.messaging",
    NULL
};

static const char *default_boost_apps[] = {
    "com.tencent.mm",
    "com.tencent.mobileqq",
    "com.eg.android.AlipayGphone",
    "com.android.chrome",
    "com.google.android.youtube",
    "com.miHoYo.GenshinImpact",
    "com.tencent.tmgp.pubgm",
    "com.netease.hero",
    NULL
};

static void emergency_power_throttle(void);
static void apply_thermal_throttle(void);
static unsigned int get_cpu_load(int cpu);

static void init_masks(void)
{
    int i;
    
    cpumask_clear(&little_mask);
    for (i = LITTLE_START; i <= LITTLE_END; i++) {
        if (cpu_possible(i))
            cpumask_set_cpu(i, &little_mask);
    }
    
    cpumask_clear(&big_mask);
    for (i = BIG_START; i <= BIG_END; i++) {
        if (cpu_possible(i))
            cpumask_set_cpu(i, &big_mask);
    }
    
    cpumask_copy(&all_mask, cpu_possible_mask);
    
    cpumask_copy(&screen_off_mask, &little_mask);
}

static unsigned int get_cpu_load(int cpu)
{
    unsigned long total_time, idle_time;
    static unsigned long prev_total[NR_CPUS] = {0};
    static unsigned long prev_idle[NR_CPUS] = {0};
    unsigned long delta_total, delta_idle;
    unsigned int load;
    
    if (cpu < 0 || cpu >= NR_CPUS)
        return 0;
    
#ifdef CONFIG_VIRT_CPU_ACCOUNTING_GEN
    {
        struct kernel_cpustat *kcpustat;
        kcpustat = &kcpustat_cpu(cpu);
        total_time = kcpustat->cpustat[CPUTIME_USER] +
                     kcpustat->cpustat[CPUTIME_NICE] +
                     kcpustat->cpustat[CPUTIME_SYSTEM] +
                     kcpustat->cpustat[CPUTIME_IDLE] +
                     kcpustat->cpustat[CPUTIME_IOWAIT] +
                     kcpustat->cpustat[CPUTIME_IRQ] +
                     kcpustat->cpustat[CPUTIME_SOFTIRQ];
        
        idle_time = kcpustat->cpustat[CPUTIME_IDLE] +
                    kcpustat->cpustat[CPUTIME_IOWAIT];
    }
#else
    total_time = jiffies * (cpu + 1);
    idle_time = total_time / 2;
#endif
    
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

static void set_cpu_freq(const cpumask_t *mask, unsigned int khz)
{
#ifdef CONFIG_CPU_FREQ
    int cpu;
    struct cpufreq_policy *policy;
    
    for_each_cpu(cpu, mask) {
        if (!cpu_online(cpu))
            continue;
            
        policy = cpufreq_cpu_get(cpu);
        if (!policy)
            continue;
        
        if (policy->cur != khz) {
            cpufreq_driver_target(policy, khz, CPUFREQ_RELATION_L);
        }
        
        cpufreq_cpu_put(policy);
    }
#endif
}

static void set_all_big_core_freq(unsigned int khz)
{
    set_cpu_freq(&big_mask, khz);
}

static void set_all_little_core_freq(unsigned int khz)
{
    set_cpu_freq(&little_mask, khz);
}

static void freeze_big_cores(bool freeze)
{
#ifdef CONFIG_HOTPLUG_CPU
    int cpu;
    
    for_each_cpu(cpu, &big_mask) {
        if (freeze) {
            if (cpu_online(cpu))
                cpu_down(cpu);
        } else {
            if (!cpu_online(cpu))
                cpu_up(cpu);
        }
    }
#endif
}

static bool get_package_name(pid_t pid, char *buf, size_t buf_size)
{
    char path[64];
    struct file *fp = NULL;
    loff_t pos = 0;
    ssize_t len;
    char cmdline[MAX_CMD_LINE_LEN];
    char *pkg_end, *pkg_name;
    
    if (!buf || buf_size == 0)
        return false;
    
    snprintf(path, sizeof(path), "/proc/%d/cmdline", pid);
    
    fp = filp_open(path, O_RDONLY, 0);
    if (IS_ERR(fp)) {
        return false;
    }
    
    len = kernel_read(fp, cmdline, sizeof(cmdline) - 1, &pos);
    filp_close(fp, NULL);
    
    if (len <= 0) {
        return false;
    }
    
    cmdline[len] = '\0';
    
    pkg_end = strchr(cmdline, ' ');
    if (pkg_end) {
        *pkg_end = '\0';
    }
    
    pkg_name = strrchr(cmdline, '/');
    if (pkg_name) {
        pkg_name++;
    } else {
        pkg_name = cmdline;
    }
    
    strncpy(buf, pkg_name, buf_size - 1);
    buf[buf_size - 1] = '\0';
    
    return true;
}

static bool is_notification_app(const char *package_name)
{
    int i;
    
    if (!package_name)
        return false;
    
    for (i = 0; default_notification_apps[i] != NULL; i++) {
        if (strstr(package_name, default_notification_apps[i])) {
            return true;
        }
    }
    
    if (strstr(package_name, ".provider") ||
        strstr(package_name, ".service") ||
        strstr(package_name, "android.")) {
        return true;
    }
    
    return false;
}

static bool is_whitelisted_app(const char *package_name)
{
    int i;
    
    if (!package_name)
        return false;
    
    mutex_lock(&whitelist_lock);
    
    for (i = 0; default_boost_apps[i] != NULL; i++) {
        if (strstr(package_name, default_boost_apps[i])) {
            mutex_unlock(&whitelist_lock);
            return true;
        }
    }
    
    for (i = 0; i < whitelist_count; i++) {
        if (app_whitelist[i] && strstr(package_name, app_whitelist[i])) {
            mutex_unlock(&whitelist_lock);
            return true;
        }
    }
    
    mutex_unlock(&whitelist_lock);
    return false;
}

static unsigned long get_system_power_uw(void)
{
    unsigned long power = 0;
    int cpu;
    unsigned int freq, load;
    unsigned long coeff;
    
    {
        struct power_supply *psy = NULL;
        union power_supply_propval val;
        union power_supply_propval volt_val;
        
        val.intval = 0;
        volt_val.intval = 0;
        
        psy = power_supply_get_by_name("battery");
        if (!psy)
            psy = power_supply_get_by_name("Battery");
        if (!psy)
            psy = power_supply_get_by_name("main");
        
        if (psy) {
            if (!power_supply_get_property(psy, POWER_SUPPLY_PROP_POWER_NOW, &val)) {
                power = val.intval;
            }
            if (!power && !power_supply_get_property(psy, POWER_SUPPLY_PROP_CURRENT_NOW, &val)) {
                if (!power_supply_get_property(psy, POWER_SUPPLY_PROP_VOLTAGE_NOW, &volt_val)) {
                    power = (val.intval * volt_val.intval) / 1000000;
                }
            }
            power_supply_put(psy);
        }
    }
    
    if (power == 0) {
        for_each_online_cpu(cpu) {
            struct cpufreq_policy *policy;
            policy = cpufreq_cpu_get(cpu);
            if (policy) {
                freq = policy->cur;
                load = get_cpu_load(cpu);
                
                coeff = cpumask_test_cpu(cpu, &big_mask) ? 25 : 15;
                power += (freq / 1000) * load * coeff;
                
                cpufreq_cpu_put(policy);
            }
        }
        
        power += 1000000;
    }
    
    return power;
}

static void update_power_statistics(void)
{
    unsigned long current_power = get_system_power_uw();
    unsigned long sum = 0;
    int i;
    
    power_samples[power_sample_index] = current_power;
    power_sample_index = (power_sample_index + 1) % ARRAY_SIZE(power_samples);
    if (power_sample_count < ARRAY_SIZE(power_samples)) {
        power_sample_count++;
    }
    
    for (i = 0; i < power_sample_count; i++) {
        sum += power_samples[i];
    }
    avg_power_uw = sum / power_sample_count;
    
    if (current_power > max_power_uw) {
        max_power_uw = current_power;
    }
    
    last_power_uw = current_power;
    
    if (avg_power_uw > POWER_THRESHOLD_HIGH * 1000) {
        if (!full_power_mode && screen_on) {
            full_power_mode = true;
            pr_warn("frame_aware_unfair: High power consumption detected: %lu uW, entering full power mode\n",
                   avg_power_uw);
            
            queue_work(fa_wq, &full_power_work);
        }
    } else if (avg_power_uw < POWER_THRESHOLD_MID * 1000) {
        if (full_power_mode) {
            full_power_mode = false;
            pr_info("frame_aware_unfair: Power consumption back to normal: %lu uW, exiting full power mode\n",
                   avg_power_uw);
        }
    }
    
    if (avg_power_uw > POWER_THRESHOLD_CRITICAL * 1000) {
        if (!power_emergency_mode) {
            power_emergency_mode = true;
            pr_emerg("frame_aware_unfair: Critical power consumption: %lu uW, emergency throttle!\n",
                    avg_power_uw);
            
            emergency_power_throttle();
        }
    } else if (avg_power_uw < POWER_THRESHOLD_HIGH * 1000) {
        if (power_emergency_mode) {
            power_emergency_mode = false;
            pr_info("frame_aware_unfair: Power emergency cleared\n");
        }
    }
}

static void emergency_power_throttle(void)
{
    struct task_struct *p;
    
    set_all_little_core_freq(LOCK_FREQ_KHZ);
    set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    if (&pc_set_persistent_limit)
        pc_set_persistent_limit(LOCK_FREQ_KHZ);
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        set_user_nice(p, 19);
        set_cpus_allowed_ptr(p, &little_mask);
    }
    rcu_read_unlock();
    
    freeze_big_cores(true);
    
    pr_emerg("frame_aware_unfair: Emergency power throttle applied\n");
}

static int get_cpu_temperature(void)
{
    int temp = 0;
    int i;
    const char *tz_names[] = {
        "cpu-thermal",
        "cpu_thermal",
        "soc_thermal",
        "therm_est",
        "virtual-thermal",
        NULL
    };
    
#ifdef CONFIG_THERMAL
    struct thermal_zone_device *tz = NULL;
    
    for (i = 0; tz_names[i] != NULL; i++) {
        tz = thermal_zone_get_zone_by_name(tz_names[i]);
        if (!IS_ERR(tz)) {
            int ret = thermal_zone_get_temp(tz, &temp);
            if (!ret) {
                last_temperature = temp / 1000;
                break;
            }
        }
    }
#endif
    
    return last_temperature;
}

static void check_thermal_status(void)
{
    int temp = get_cpu_temperature();
    
    if (temp > THERMAL_THRESHOLD) {
        if (!thermal_throttle_mode) {
            thermal_throttle_mode = true;
            pr_warn("frame_aware_unfair: High temperature detected: %d°C, thermal throttling\n", temp);
            
            apply_thermal_throttle();
        }
    } else if (temp < THERMAL_THRESHOLD - 5) {
        if (thermal_throttle_mode) {
            thermal_throttle_mode = false;
            pr_info("frame_aware_unfair: Temperature back to normal: %d°C\n", temp);
        }
    }
}

static void apply_thermal_throttle(void)
{
    struct task_struct *p;
    unsigned int limit_freq = BIG_CORE_MID_FREQ_KHZ;
    
    if (last_temperature > THERMAL_THRESHOLD + 10) {
        limit_freq = BIG_CORE_IDLE_FREQ_KHZ;
    }
    
    set_all_big_core_freq(limit_freq);
    set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    if (&pc_set_persistent_limit)
        pc_set_persistent_limit(limit_freq);
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        if (p->static_prio < DEFAULT_PRIO) {
            set_user_nice(p, DEFAULT_PRIO);
        }
    }
    rcu_read_unlock();
}

static void full_power_work_func(struct work_struct *work)
{
    struct task_struct *p;
    
    if (!full_power_mode || !screen_on)
        return;
    
    pr_info("frame_aware_unfair: Entering full power mode\n");
    
    if (&pc_set_persistent_limit)
        pc_set_persistent_limit(BIG_CORE_MAX_FREQ_KHZ);
    
    freeze_big_cores(false);
    
    set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
    set_all_little_core_freq(LITTLE_CORE_BOOST_KHZ);
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        set_user_nice(p, -20);
        set_cpus_allowed_ptr(p, &all_mask);
    }
    rcu_read_unlock();
    
    pr_info("frame_aware_unfair: Full power mode activated\n");
}

static void exit_full_power_mode(void)
{
    if (full_power_mode) {
        full_power_mode = false;
        pr_info("frame_aware_unfair: Exiting full power mode\n");
    }
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
    
    if (!get_package_name(task->pid, package_name, sizeof(package_name))) {
        return;
    }
    
    info = find_task_info(task->pid);
    if (!info) {
        info = kzalloc(sizeof(*info), GFP_ATOMIC);
        if (!info)
            return;
            
        info->pid = task->pid;
        info->is_foreground = is_foreground;
        strncpy(info->package_name, package_name, sizeof(info->package_name) - 1);
        info->package_name[sizeof(info->package_name) - 1] = '\0';
        info->is_notification = is_notification_app(package_name);
        info->is_whitelisted = is_whitelisted_app(package_name);
        info->last_boost_jiffies = 0;
        info->is_heavy_task = false;
        info->avg_power_uw = 0;
        info->last_power_check = jiffies;
        
        spin_lock(&task_list_lock);
        list_add_tail(&info->list, &task_list);
        spin_unlock(&task_list_lock);
    } else {
        info->is_foreground = is_foreground;
        if (strcmp(info->package_name, package_name) != 0) {
            strncpy(info->package_name, package_name, sizeof(info->package_name) - 1);
            info->package_name[sizeof(info->package_name) - 1] = '\0';
            info->is_notification = is_notification_app(package_name);
            info->is_whitelisted = is_whitelisted_app(package_name);
        }
    }
}

static bool is_heavy_task(struct task_struct *p, struct task_info *info)
{
    unsigned int load;
    
    if (!info)
        return false;
    
    if (info->avg_power_uw > POWER_THRESHOLD_MID * 1000) {
        return true;
    }
    
    load = get_cpu_load(task_cpu(p));
    if (load > LOAD_THRESHOLD_HIGH) {
        return true;
    }
    
    return false;
}

static void update_task_power(struct task_struct *p, struct task_info *info)
{
    unsigned long now;
    unsigned int cpu;
    struct cpufreq_policy *policy;
    
    if (!info || !p)
        return;
    
    now = jiffies;
    
    if (time_after(now, info->last_power_check + msecs_to_jiffies(1000))) {
        cpu = task_cpu(p);
        policy = cpufreq_cpu_get(cpu);
        if (policy) {
            unsigned int freq = policy->cur;
            unsigned int load = get_cpu_load(cpu);
            unsigned long cpu_power = (freq / 1000) * load * 15;
            info->avg_power_uw = cpu_power / 10;
            cpufreq_cpu_put(policy);
        }
        
        info->last_power_check = now;
    }
}

static void schedule_notification_app(struct task_struct *p, struct task_info *info)
{
    set_user_nice(p, 19);
    set_cpus_allowed_ptr(p, &little_mask);
}

static void schedule_whitelist_app(struct task_struct *p, struct task_info *info)
{
    unsigned int big_core_load;
    
    if (!info)
        return;
    
    set_user_nice(p, -20);
    set_cpus_allowed_ptr(p, &big_mask);
    
    big_core_load = get_big_core_load();
    
    if (big_core_load > BIG_CORE_LOAD_THRESHOLD) {
        if (big_core_load > ALL_CORE_LOAD_THRESHOLD) {
            set_cpus_allowed_ptr(p, &all_mask);
        }
    }
}

static void schedule_normal_app_enhanced(struct task_struct *p, struct task_info *info)
{
    unsigned long boost_end_time;
    unsigned int big_core_load;
    bool is_heavy;
    unsigned int task_load;
    
    if (!info)
        return;
    
    update_task_power(p, info);
    
    is_heavy = is_heavy_task(p, info);
    boost_end_time = info->last_boost_jiffies + msecs_to_jiffies(BOOST_DURATION_MS);
    
    if (time_before(jiffies, boost_end_time)) {
        set_user_nice(p, -5);
        set_cpus_allowed_ptr(p, &little_mask);
        
        if (info->avg_power_uw > POWER_THRESHOLD_LOW * 1000) {
            set_cpus_allowed_ptr(p, &big_mask);
        }
    } else {
        task_load = get_cpu_load(task_cpu(p));
        
        if (is_heavy || info->avg_power_uw > POWER_THRESHOLD_MID * 1000) {
            set_user_nice(p, -15);
            set_cpus_allowed_ptr(p, &big_mask);
            
            if (get_big_core_load() > ALL_CORE_LOAD_THRESHOLD) {
                set_cpus_allowed_ptr(p, &all_mask);
            }
        } else if (task_load < LOAD_THRESHOLD_LOW) {
            set_user_nice(p, 0);
            set_cpus_allowed_ptr(p, &little_mask);
        } else if (task_load < LOAD_THRESHOLD_HIGH) {
            big_core_load = get_big_core_load();
            
            if (big_core_load < BIG_CORE_LOAD_THRESHOLD) {
                set_user_nice(p, -10);
                set_cpus_allowed_ptr(p, &big_mask);
            } else {
                set_user_nice(p, -5);
                set_cpus_allowed_ptr(p, &little_mask);
            }
        } else {
            set_user_nice(p, -15);
            set_cpus_allowed_ptr(p, &big_mask);
            
            if (get_big_core_load() > ALL_CORE_LOAD_THRESHOLD) {
                set_cpus_allowed_ptr(p, &all_mask);
            }
        }
    }
}

static void handle_screen_off(void)
{
    struct task_struct *p;
    struct task_info *info;
    int processed = 0;
    
    if (!screen_on && !screen_off_processed) {
        freeze_big_cores(true);
        
        set_all_little_core_freq(LOCK_FREQ_KHZ);
        if (&pc_set_persistent_limit)
            pc_set_persistent_limit(LOCK_FREQ_KHZ);
        
        rcu_read_lock();
        for_each_process(p) {
            if (!p->mm || p->flags & PF_KTHREAD)
                continue;
            
            info = find_task_info(p->pid);
            if (info && info->is_notification) {
                set_user_nice(p, 19);
                set_cpus_allowed_ptr(p, &screen_off_mask);
                processed++;
            } else {
                set_user_nice(p, 20);
            }
        }
        rcu_read_unlock();
        
        screen_off_processed = true;
        pr_info("frame_aware_unfair: Screen off processed, %d tasks kept\n", processed);
    }
}

static void adjust_frequencies_with_power(void)
{
    unsigned int big_load = get_big_core_load();
    unsigned int little_load = get_cpu_load(LITTLE_START);
    
    if (!screen_on) {
        set_all_little_core_freq(LOCK_FREQ_KHZ);
        set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        return;
    }
    
    if (full_power_mode) {
        set_all_little_core_freq(LITTLE_CORE_BOOST_KHZ);
        set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
        return;
    }
    
    if (power_emergency_mode) {
        set_all_little_core_freq(LOCK_FREQ_KHZ);
        set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        return;
    }
    
    if (avg_power_uw < POWER_THRESHOLD_LOW * 1000) {
        set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    } else if (avg_power_uw < POWER_THRESHOLD_MID * 1000) {
        if (little_load < LOAD_THRESHOLD_LOW) {
            set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        } else if (little_load < LOAD_THRESHOLD_HIGH) {
            set_all_little_core_freq((LITTLE_CORE_MIN_KHZ + LITTLE_CORE_MAX_KHZ) / 2);
        } else {
            set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        }
        
        if (big_load < LOAD_THRESHOLD_LOW) {
            set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
        } else if (big_load < LOAD_THRESHOLD_HIGH) {
            set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
        } else {
            set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
        }
    } else if (avg_power_uw < POWER_THRESHOLD_HIGH * 1000) {
        if (little_load > LOAD_THRESHOLD_MID) {
            set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        } else {
            set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        }
        
        if (big_load > LOAD_THRESHOLD_MID) {
            set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
        } else {
            set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
        }
    }
}

static void schedule_tasks_enhanced(void)
{
    struct task_struct *p;
    struct task_info *info;
    
    if (!screen_on) {
        handle_screen_off();
        return;
    }
    
    screen_off_processed = false;
    
    if (full_power_mode) {
        return;
    }
    
    if (power_emergency_mode) {
        return;
    }
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        update_task_info(p);
    }
    rcu_read_unlock();
    
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        
        info = find_task_info(p->pid);
        if (!info)
            continue;
        
        if (info->is_foreground && info->avg_power_uw > POWER_THRESHOLD_HIGH * 1000) {
            full_power_mode = true;
            queue_work(fa_wq, &full_power_work);
            break;
        }
        
        if (info->is_notification) {
            schedule_notification_app(p, info);
        } else if (info->is_whitelisted) {
            schedule_whitelist_app(p, info);
        } else {
            schedule_normal_app_enhanced(p, info);
        }
    }
    rcu_read_unlock();
    
    adjust_frequencies_with_power();
}

static void check_work_func(struct work_struct *work)
{
    struct task_info *info, *tmp;
    struct task_struct *task;
    
    schedule_tasks_enhanced();
    
    spin_lock(&task_list_lock);
    list_for_each_entry_safe(info, tmp, &task_list, list) {
        rcu_read_lock();
        task = find_task_by_vpid(info->pid);
        if (!task) {
            list_del(&info->list);
            kfree(info);
        }
        rcu_read_unlock();
    }
    spin_unlock(&task_list_lock);
    
    queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
}

static void boost_work_func(struct work_struct *work)
{
    struct task_info *info;
    
    if (fg_pid == 0)
        return;
    
    info = find_task_info(fg_pid);
    if (info) {
        info->last_boost_jiffies = jiffies;
        
        if (info->is_whitelisted) {
            set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
            if (&pc_set_persistent_limit)
                pc_set_persistent_limit(BIG_CORE_BOOST_HZ_KHZ);
            pr_debug("frame_aware_unfair: Whitelist app boosted\n");
        } else {
            set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
            if (&pc_set_persistent_limit)
                pc_set_persistent_limit(BIG_CORE_MID_FREQ_KHZ);
            pr_debug("frame_aware_unfair: Normal app boosted\n");
        }
    }
}

static void screen_off_work_func(struct work_struct *work)
{
    if (!screen_on) {
        handle_screen_off();
    }
}

static void power_check_work_func(struct work_struct *work)
{
    update_power_statistics();
    
    if (full_power_mode && avg_power_uw < POWER_THRESHOLD_MID * 1000) {
        exit_full_power_mode();
    }
    
    queue_delayed_work(fa_wq, &power_check_work,
                      msecs_to_jiffies(POWER_CHECK_INTERVAL_MS));
}

static void thermal_check_work_func(struct work_struct *work)
{
    check_thermal_status();
    
    queue_delayed_work(fa_wq, &thermal_check_work,
                      msecs_to_jiffies(5000));
}

static void boot_complete_work_func(struct work_struct *work)
{
    boot_complete = true;
    pr_info("frame_aware_unfair: Boot complete\n");
}

static int fa_input_connect(struct input_handler *handler,
                            struct input_dev *dev,
                            const struct input_device_id *id)
{
    struct input_handle *h;
    int err;
    
    h = kzalloc(sizeof(*h), GFP_KERNEL);
    if (!h)
        return -ENOMEM;
    
    h->dev = dev;
    h->handler = handler;
    h->name = "frame_aware_unfair";
    
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
    if (!screen_on)
        return;
    
    if (type == EV_ABS || type == EV_KEY || type == EV_SYN) {
        last_touch_jiffies = jiffies;
        
        queue_work(fa_wq, &boost_work);
        
        mod_delayed_work(fa_wq, &check_work, 0);
    }
}

static const struct input_device_id fa_ids[] = {
    { .driver_info = 1 },
    { }
};

static struct input_handler fa_input_handler = {
    .event = fa_input_event,
    .connect = fa_input_connect,
    .disconnect = fa_input_disconnect,
    .name = "frame_aware_unfair",
    .id_table = fa_ids,
};

static int fb_notif_call(struct notifier_block *nb,
                         unsigned long event, void *data)
{
    int *blankp;
    
    if (event != FB_EVENT_BLANK)
        return NOTIFY_DONE;
    
    blankp = data ? *(int **)(&data) : NULL;
    if (!blankp)
        return NOTIFY_DONE;
    
    if (*blankp == FB_BLANK_UNBLANK) {
        screen_on = true;
        screen_off_processed = false;
        last_touch_jiffies = jiffies;
        
        freeze_big_cores(false);
        
        set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
        set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
        if (&pc_set_persistent_limit)
            pc_set_persistent_limit(BIG_CORE_MID_FREQ_KHZ);
        
        queue_work(fa_wq, &boost_work);
        
        queue_delayed_work(fa_wq, &check_work, 0);
        
        pr_info("frame_aware_unfair: Screen on\n");
    } else {
        screen_on = false;
        screen_off_jiffies = jiffies;
        
        cancel_delayed_work(&screen_off_work);
        queue_delayed_work(fa_wq, &screen_off_work,
                          msecs_to_jiffies(SCREEN_OFF_DELAY_MS));
        
        pr_info("frame_aware_unfair: Screen off, processing in %d ms\n",
                SCREEN_OFF_DELAY_MS);
    }
    
    return NOTIFY_OK;
}

static struct notifier_block fb_notifier = {
    .notifier_call = fb_notif_call,
};

static ssize_t fg_pid_show(struct kobject *k, struct kobj_attribute *a, char *buf)
{
    return sprintf(buf, "%d\n", fg_pid);
}

static ssize_t fg_pid_store(struct kobject *k, struct kobj_attribute *a,
                            const char *buf, size_t count)
{
    pid_t v;
    
    if (kstrtoint(buf, 10, &v) == 0) {
        mutex_lock(&fg_lock);
        fg_pid = v;
        
        if (screen_on) {
            queue_work(fa_wq, &boost_work);
        }
        
        mutex_unlock(&fg_lock);
    }
    
    return count;
}

static struct kobj_attribute fg_attr =
    __ATTR(fg_pid, 0644, fg_pid_show, fg_pid_store);

static ssize_t power_monitor_show(struct kobject *k, struct kobj_attribute *a, char *buf)
{
    int len = 0;
    unsigned int avg_watts = avg_power_uw / 1000000;
    unsigned int avg_milliwatts = (avg_power_uw % 1000000) / 1000;
    unsigned int max_watts = max_power_uw / 1000000;
    unsigned int max_milliwatts = (max_power_uw % 1000000) / 1000;
    
    len += sprintf(buf + len, "Current Power: %lu uW\n", last_power_uw);
    len += sprintf(buf + len, "Average Power: %u.%03u W\n", 
                   avg_watts, avg_milliwatts);
    len += sprintf(buf + len, "Max Power: %u.%03u W\n",
                   max_watts, max_milliwatts);
    len += sprintf(buf + len, "Power Mode: ");
    
    if (avg_power_uw > POWER_THRESHOLD_HIGH * 1000) {
        len += sprintf(buf + len, "High\n");
    } else if (avg_power_uw > POWER_THRESHOLD_MID * 1000) {
        len += sprintf(buf + len, "Medium\n");
    } else {
        len += sprintf(buf + len, "Low\n");
    }
    
    len += sprintf(buf + len, "Emergency Mode: %s\n",
                   power_emergency_mode ? "Yes" : "No");
    len += sprintf(buf + len, "Full Power Mode: %s\n",
                   full_power_mode ? "Yes" : "No");
    len += sprintf(buf + len, "Temperature: %d°C\n",
                   last_temperature);
    len += sprintf(buf + len, "Thermal Throttle: %s\n",
                   thermal_throttle_mode ? "Yes" : "No");
    
    return len;
}

static ssize_t power_monitor_store(struct kobject *k, struct kobj_attribute *a,
                                   const char *buf, size_t count)
{
    unsigned long power_limit;
    
    if (kstrtoul(buf, 10, &power_limit) == 0) {
        pr_info("frame_aware_unfair: Setting power limit to %lu uW\n", power_limit);
    }
    
    return count;
}

static struct kobj_attribute power_attr =
    __ATTR(power_monitor, 0644, power_monitor_show, power_monitor_store);

static int __init fa_init(void)
{
    int rc;
    
    pr_info("frame_aware_unfair: Initializing Enhanced Version...\n");
    
    init_masks();
    
    fa_wq = create_singlethread_workqueue("frame_aware_wq");
    if (!fa_wq) {
        pr_err("frame_aware_unfair: Failed to create workqueue\n");
        return -ENOMEM;
    }
    
    INIT_DELAYED_WORK(&check_work, check_work_func);
    INIT_DELAYED_WORK(&screen_off_work, screen_off_work_func);
    INIT_WORK(&boost_work, boost_work_func);
    INIT_DELAYED_WORK(&boot_complete_work, boot_complete_work_func);
    INIT_DELAYED_WORK(&power_check_work, power_check_work_func);
    INIT_DELAYED_WORK(&thermal_check_work, thermal_check_work_func);
    INIT_WORK(&full_power_work, full_power_work_func);
    
    rc = fb_register_client(&fb_notifier);
    if (rc) {
        pr_warn("frame_aware_unfair: fb_register_client failed %d\n", rc);
    }
    
    rc = input_register_handler(&fa_input_handler);
    if (rc) {
        pr_warn("frame_aware_unfair: input_register_handler failed %d\n", rc);
    }
    
    fa_kobj = kobject_create_and_add("frame_aware", kernel_kobj);
    if (fa_kobj) {
        if (sysfs_create_file(fa_kobj, &fg_attr.attr)) {
            pr_warn("frame_aware_unfair: failed to create sysfs fg_pid\n");
        }
        
        if (sysfs_create_file(fa_kobj, &power_attr.attr)) {
            pr_warn("frame_aware_unfair: failed to create sysfs power_monitor\n");
        }
    } else {
        pr_warn("frame_aware_unfair: failed to create kobject\n");
    }
    
    last_touch_jiffies = jiffies;
    screen_on = true;
    power_check_jiffies = jiffies;
    thermal_check_jiffies = jiffies;
    
    queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
    queue_delayed_work(fa_wq, &power_check_work,
                      msecs_to_jiffies(POWER_CHECK_INTERVAL_MS));
    queue_delayed_work(fa_wq, &thermal_check_work,
                      msecs_to_jiffies(5000));
    
    schedule_delayed_work(&boot_complete_work, msecs_to_jiffies(30000));
    
    pr_info("frame_aware_unfair: Enhanced Module initialized with power monitoring\n");
    
    return 0;
}

static void __exit fa_exit(void)
{
    struct task_info *info, *tmp;
    
    pr_info("frame_aware_unfair: Exiting...\n");
    
    cancel_delayed_work_sync(&check_work);
    cancel_delayed_work_sync(&screen_off_work);
    cancel_work_sync(&boost_work);
    cancel_delayed_work_sync(&boot_complete_work);
    cancel_delayed_work_sync(&power_check_work);
    cancel_delayed_work_sync(&thermal_check_work);
    cancel_work_sync(&full_power_work);
    
    if (fa_wq) {
        flush_workqueue(fa_wq);
        destroy_workqueue(fa_wq);
    }
    
    spin_lock(&task_list_lock);
    list_for_each_entry_safe(info, tmp, &task_list, list) {
        list_del(&info->list);
        kfree(info);
    }
    spin_unlock(&task_list_lock);
    
    if (app_whitelist) {
        int i;
        mutex_lock(&whitelist_lock);
        for (i = 0; i < whitelist_count; i++) {
            kfree(app_whitelist[i]);
        }
        kfree(app_whitelist);
        app_whitelist = NULL;
        whitelist_count = 0;
        mutex_unlock(&whitelist_lock);
    }
    
    input_unregister_handler(&fa_input_handler);
    fb_unregister_client(&fb_notifier);
    
    if (fa_kobj) {
        sysfs_remove_file(fa_kobj, &fg_attr.attr);
        sysfs_remove_file(fa_kobj, &power_attr.attr);
        kobject_put(fa_kobj);
    }
    
    pr_info("frame_aware_unfair: Module unloaded\n");
}

module_init(fa_init);
module_exit(fa_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Unfair Power Scheduler - Power Aware Enhanced Version");
MODULE_DESCRIPTION("Android-aware task scheduler with power and thermal monitoring");
