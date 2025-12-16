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
#include <linux/freezer.h>
#include <linux/kallsyms.h>
#include <linux/vmalloc.h>
#include <linux/pid.h>
#include <linux/sched/task.h>

#define APP_CATEGORY_SYSTEM 0
#define APP_CATEGORY_BACKGROUND 1
#define APP_CATEGORY_INTERACTIVE 2
#define APP_CATEGORY_GAME 3
#define APP_CATEGORY_VIDEO 4
#define APP_CATEGORY_BROWSER 5
#define APP_CATEGORY_SOCIAL 6

#define MODE_WHITELIST 0

#define LOCK_FREQ_KHZ 300000U
#define BIG_CORE_IDLE_FREQ_KHZ 300000U
#define BIG_CORE_MID_FREQ_KHZ 900000U
#define BIG_CORE_BOOST_HZ_KHZ 1500000U
#define BIG_CORE_MAX_FREQ_KHZ 2000000U
#define LITTLE_CORE_MIN_KHZ 400000U
#define LITTLE_CORE_MAX_KHZ 1600000U
#define LITTLE_CORE_BOOST_KHZ 2000000U

#define LITTLE_START 0
#define LITTLE_END 3
#define BIG_START 4
#define BIG_END 7

#define BOOST_DURATION_MS 3000
#define SCREEN_OFF_DELAY_MS 1000
#define IDLE_NO_TOUCH_DELAY_MS 5000
#define CHECK_INTERVAL_MS 500
#define POWER_CHECK_INTERVAL_MS 5000
#define MAX_TASK_CHECK 50

#define LOAD_THRESHOLD_LOW 30
#define LOAD_THRESHOLD_MID 50
#define LOAD_THRESHOLD_HIGH 70

#define POWER_THRESHOLD_LOW 2000
#define POWER_THRESHOLD_MID 3000
#define POWER_THRESHOLD_HIGH 4500
#define POWER_THRESHOLD_CRITICAL 6000

#define THERMAL_THRESHOLD 75
#define BIG_CORE_LOAD_THRESHOLD 70
#define ALL_CORE_LOAD_THRESHOLD 75

#define WHITELIST_FILE_PATH "/data/media/0/Android/boost.json"
#define MAX_WHITELIST_APPS 100
#define MAX_PACKAGE_NAME_LEN 256
#define MAX_CMD_LINE_LEN 512
#define MAX_JSON_FILE_SIZE 4096
#define MAX_APP_NAME_LEN 256

#define FA_DEFAULT_NICE 0
#define MAX_PROFILE_DATA_SIZE (64 * 1024 * 1024)

#define PID_CHECK_INTERVAL_MS 2000
#define THERMAL_RETRY_DELAY_MS 100
#define MAX_PROCESS_SCAN 50
#define PID_DETECT_TIMEOUT_MS 50

#define CLUSTER_TYPE_LITTLE 0
#define CLUSTER_TYPE_BIG 1
#define CLUSTER_TYPE_ALL 2

typedef int (*pc_set_persistent_limit_func)(unsigned int khz);
static pc_set_persistent_limit_func pc_set_persistent_limit_ptr = NULL;

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
static bool screen_idle_mode = false;
static bool input_handler_registered = false;
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

static int last_temperature = 25;

static char **app_whitelist = NULL;
static int whitelist_count = 0;
static int current_mode = MODE_WHITELIST;
static DEFINE_MUTEX(whitelist_lock);

static struct delayed_work check_work;
static struct work_struct boost_work;
static struct delayed_work screen_off_work;
static struct delayed_work boot_complete_work;
static struct delayed_work power_check_work;
static struct delayed_work thermal_check_work;
static struct work_struct full_power_work;
static struct delayed_work idle_check_work;
static struct delayed_work delayed_save_profiles_work;
static struct delayed_work pid_detect_work;
static struct workqueue_struct *fa_wq;

struct app_profile {
    char package_name[MAX_PACKAGE_NAME_LEN];
    int category;
    bool prefers_big_cores;
    bool prefers_frequency;
    unsigned int avg_cpu_usage;
    unsigned int avg_wakeups;
    unsigned long total_runtime;
    unsigned long last_update;
    int cluster_type;
    struct list_head list;
};

struct task_info {
    pid_t pid;
    char package_name[MAX_PACKAGE_NAME_LEN];
    bool is_foreground;
    bool is_whitelisted;
    bool is_notification;
    bool is_heavy_task;
    bool is_essential;
    unsigned long last_boost_jiffies;
    unsigned long last_power_check;
    unsigned long avg_power_uw;
    bool is_frozen;
    int cluster_type;
    struct list_head list;
};

static unsigned int dynamic_load_threshold = LOAD_THRESHOLD_MID;
static unsigned int dynamic_power_threshold = POWER_THRESHOLD_MID;
static bool aggressive_power_save = false;

static LIST_HEAD(task_list);
static LIST_HEAD(app_profiles);
static DEFINE_SPINLOCK(task_list_lock);
static DEFINE_SPINLOCK(app_profiles_lock);

static char *profile_data_buffer = NULL;
static size_t profile_data_size = 0;
static DEFINE_MUTEX(profile_data_lock);

static DEFINE_SPINLOCK(pid_detect_lock);
static bool pid_detect_in_progress = false;
static unsigned long pid_detect_start_jiffies = 0;

static const char *foreground_process_patterns[] = {
    "com.android.systemui",
    "com.android.launcher",
    "com.miui.home",
    "com.tencent.mm",
    "com.tencent.mobileqq",
    "com.eg.android.AlipayGphone",
    "com.android.chrome",
    "com.google.android.youtube",
    NULL
};

static const char *default_essential_apps[] = {
    "com.android.systemui",
    "com.android.phone",
    "com.android.mms",
    "com.android.providers.telephony",
    "com.android.dialer",
    "android.process.acore",
    "system_server",
    "surfaceflinger",
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
static void load_config_from_file(void);
static void free_whitelist(void);
static bool is_essential_app(const char *package_name);
static void unfreeze_all_tasks(void);
static struct task_info *find_task_info(pid_t pid);
static void enter_screen_idle_mode(void);
static void exit_screen_idle_mode(void);
static void online_all_little_cores(void);
static void analyze_application_behavior(struct task_struct *p, struct task_info *info);
static int detect_app_category(const char *package_name);
static struct app_profile *find_app_profile(const char *package_name);
static int get_app_cluster_type(const char *package_name);
static void schedule_whitelist_app_by_cluster(struct task_struct *p, struct task_info *info, int cluster_type);
static void schedule_notification_app(struct task_struct *p, struct task_info *info);
static void schedule_whitelist_app(struct task_struct *p, struct task_info *info);
static void schedule_normal_app_enhanced(struct task_struct *p, struct task_info *info);
static void adjust_frequencies_with_power(void);
static void update_power_statistics(void);
static int get_cpu_temperature(void);
static void check_thermal_status(void);
static void full_power_work_func(struct work_struct *work);
static void exit_full_power_mode(void);
static void update_task_info(struct task_struct *task);
static bool is_heavy_task(struct task_struct *p, struct task_info *info);
static void update_task_power(struct task_struct *p, struct task_info *info);
static void schedule_screen_off_mode(void);
static void schedule_screen_on_mode(void);
static void idle_check_work_func(struct work_struct *work);
static void check_work_func(struct work_struct *work);
static void boost_work_func(struct work_struct *work);
static void screen_off_work_func(struct work_struct *work);
static void power_check_work_func(struct work_struct *work);
static void thermal_check_work_func(struct work_struct *work);
static void boot_complete_work_func(struct work_struct *work);
static void delayed_save_profiles_work_func(struct work_struct *work);
static void pid_detect_work_func(struct work_struct *work);
static int fb_notif_call(struct notifier_block *nb, unsigned long event, void *data);
static int fa_input_connect(struct input_handler *handler, struct input_dev *dev, const struct input_device_id *id);
static void fa_input_disconnect(struct input_handle *handle);
static void fa_input_event(struct input_handle *handle, unsigned int type, unsigned int code, int value);
static void save_app_profiles_to_buffer(void);
static void load_app_profiles_from_buffer(void);
static ssize_t app_profiles_data_show(struct kobject *k, struct kobj_attribute *a, char *buf);
static ssize_t app_profiles_data_store(struct kobject *k, struct kobj_attribute *a, const char *buf, size_t count);
static void detect_foreground_pid_safe(void);
static int read_temperature_from_file(const char *path);
static int read_temperature_from_thermal(void);
static bool get_package_name_safe(pid_t pid, char *buf, size_t buf_size);
static bool pid_detect_timeout_check(void);
static int get_app_cluster_type_from_config(const char *package_name);
static void load_cluster_config_from_file(void);

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

static struct notifier_block fb_notifier = {
    .notifier_call = fb_notif_call,
};

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
        if (cpu_possible(i))
            cpumask_set_cpu(i, &big_mask);
    }
    cpumask_copy(&all_mask, cpu_possible_mask);
    cpumask_copy(&screen_off_mask, &little_mask);
}

static unsigned int get_cpu_load(int cpu)
{
    unsigned long total_time = 0, idle_time = 0;
    static unsigned long prev_total[NR_CPUS] = {0};
    static unsigned long prev_idle[NR_CPUS] = {0};
    unsigned long delta_total, delta_idle;
    unsigned int load = 0;
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
    total_time = jiffies;
    idle_time = jiffies / 2;
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

static void online_all_little_cores(void)
{
#ifdef CONFIG_HOTPLUG_CPU
    int cpu;
    for_each_cpu(cpu, &little_mask) {
        if (!cpu_online(cpu))
            cpu_up(cpu);
    }
#endif
}

static bool get_package_name_safe(pid_t pid, char *buf, size_t buf_size)
{
    char path[64];
    struct file *fp = NULL;
    loff_t pos = 0;
    ssize_t len;
    char cmdline[MAX_CMD_LINE_LEN];
    char *pkg_end, *pkg_name;
    
    if (!buf || buf_size == 0 || buf_size < 2)
        return false;
        
    if (pid <= 0 || pid > PID_MAX_LIMIT) {
        return false;
    }
    
    snprintf(path, sizeof(path), "/proc/%d/cmdline", pid);
    
    fp = filp_open(path, O_RDONLY | O_NONBLOCK, 0);
    if (IS_ERR(fp)) {
        return false;
    }
    
    len = kernel_read(fp, cmdline, sizeof(cmdline) - 1, &pos);
    filp_close(fp, NULL);
    
    if (len <= 0) {
        return false;
    }
    
    if (len >= (ssize_t)sizeof(cmdline))
        len = sizeof(cmdline) - 1;
    cmdline[len] = '\0';
    
    if (cmdline[0] == '\0') {
        return false;
    }
    
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
    
    if (strlen(pkg_name) == 0) {
        return false;
    }
    
    strncpy(buf, pkg_name, buf_size - 1);
    buf[buf_size - 1] = '\0';
    
    if (strlen(buf) < 3) {
        return false;
    }
    
    return true;
}

static bool is_essential_app(const char *package_name)
{
    int i;
    if (!package_name)
        return false;
    for (i = 0; default_essential_apps[i] != NULL; i++) {
        if (strstr(package_name, default_essential_apps[i])) {
            return true;
        }
    }
    if (strstr(package_name, "system") ||
        strstr(package_name, ".provider") ||
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
    for (i = 0; i < whitelist_count; i++) {
        if (app_whitelist[i] && strstr(package_name, app_whitelist[i])) {
            mutex_unlock(&whitelist_lock);
            return true;
        }
    }
    mutex_unlock(&whitelist_lock);
    return false;
}

static void unfreeze_all_tasks(void)
{
    struct task_struct *p;
    struct task_info *info;
    spin_lock(&task_list_lock);
    list_for_each_entry(info, &task_list, list) {
        info->is_frozen = false;
    }
    spin_unlock(&task_list_lock);
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        if (p->pid <= 100)
            continue;
        set_user_nice(p, 0);
        set_cpus_allowed_ptr(p, &all_mask);
    }
    rcu_read_unlock();
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

static int get_app_cluster_type_from_config(const char *package_name)
{
    int i;
    static bool config_loaded = false;
    static struct {
        char *package_name;
        int cluster_type;
    } cluster_config[MAX_WHITELIST_APPS];
    static int config_count = 0;
    
    if (!config_loaded) {
        load_cluster_config_from_file();
        config_loaded = true;
    }
    
    if (!package_name)
        return -1;

    for (i = 0; i < config_count; i++) {
        if (cluster_config[i].package_name && 
            strstr(package_name, cluster_config[i].package_name)) {
            return cluster_config[i].cluster_type;
        }
    }
    
    return -1;
}

static void load_cluster_config_from_file(void)
{
    struct file *fp = NULL;
    loff_t pos = 0;
    char *buffer = NULL;
    ssize_t len;
    char *line, *end;
    int cluster_index = -1;
    static struct {
        char *package_name;
        int cluster_type;
    } cluster_config[MAX_WHITELIST_APPS];
    static int config_count = 0;
    
    memset(cluster_config, 0, sizeof(cluster_config));
    config_count = 0;
    
    fp = filp_open("/data/media/0/Android/cluster.json", O_RDONLY, 0);
    if (IS_ERR(fp)) {
        printk(KERN_INFO "FrameAware: No cluster config file\n");
        return;
    }
    
    buffer = kzalloc(MAX_JSON_FILE_SIZE, GFP_KERNEL);
    if (!buffer) {
        filp_close(fp, NULL);
        return;
    }
    
    len = kernel_read(fp, buffer, MAX_JSON_FILE_SIZE - 1, &pos);
    filp_close(fp, NULL);
    
    if (len <= 0) {
        kfree(buffer);
        return;
    }
    
    buffer[len] = '\0';
    line = buffer;
    
    while (*line) {
        while (*line && (*line == ' ' || *line == '\t' || *line == '\n' ||
                        *line == '\r' || *line == '"')) {
            line++;
        }
        
        if (!*line)
            break;
        
        if (*line == '[') {
            cluster_index++;
            line++;
            continue;
        } else if (*line == ']') {
            line++;
            continue;
        } else if (*line == ',') {
            line++;
            continue;
        }
        
        if (cluster_index >= 0 && cluster_index <= 2) {
            end = line;
            while (*end && *end != ' ' && *end != '\t' && *end != '\n' &&
                   *end != '\r' && *end != '[' && *end != ']' &&
                   *end != '"' && *end != ',') {
                end++;
            }
            
            if (end > line && config_count < MAX_WHITELIST_APPS) {
                int app_len = end - line;
                if (app_len > 0 && app_len < MAX_PACKAGE_NAME_LEN) {
                    cluster_config[config_count].package_name = kzalloc(app_len + 1, GFP_KERNEL);
                    if (cluster_config[config_count].package_name) {
                        strncpy(cluster_config[config_count].package_name, line, app_len);
                        cluster_config[config_count].package_name[app_len] = '\0';
                        cluster_config[config_count].cluster_type = cluster_index;
                        config_count++;
                    }
                }
            }
            line = end;
        } else {
            line++;
        }
    }
    
    kfree(buffer);
    printk(KERN_INFO "FrameAware: Loaded %d cluster configs\n", config_count);
}

static int get_app_cluster_type(const char *package_name)
{
    struct app_profile *profile = find_app_profile(package_name);
    int cluster_type;
    
    if (!package_name)
        return -1;
    
    cluster_type = get_app_cluster_type_from_config(package_name);
    
    if (cluster_type >= 0)
        return cluster_type;

    if (profile && profile->cluster_type >= 0)
        return profile->cluster_type;
    
    if (is_whitelisted_app(package_name)) {
        if (detect_app_category(package_name) == APP_CATEGORY_GAME)
            return CLUSTER_TYPE_ALL;
        else
            return CLUSTER_TYPE_BIG;
    }
    
    return -1;
}

static void schedule_whitelist_app_by_cluster(struct task_struct *p, struct task_info *info, int cluster_type)
{
    if (!info)
        return;
    
    switch (cluster_type) {
        case CLUSTER_TYPE_LITTLE:
            set_user_nice(p, 0);
            set_cpus_allowed_ptr(p, &little_mask);
            break;
        case CLUSTER_TYPE_BIG:
            set_user_nice(p, -10);
            set_cpus_allowed_ptr(p, &big_mask);
            break;
        case CLUSTER_TYPE_ALL:
            set_user_nice(p, -20);
            set_cpus_allowed_ptr(p, &all_mask);
            break;
        default:
            schedule_whitelist_app(p, info);
            break;
    }
}

static void load_config_from_file(void)
{
    struct file *fp = NULL;
    loff_t pos = 0;
    char *buffer = NULL;
    ssize_t len;
    char *line, *end;
    int i, j;
    int mode_found = 0;
    int array_depth = 0;
    
    mutex_lock(&whitelist_lock);
    
    free_whitelist();
    current_mode = MODE_WHITELIST;
    
    fp = filp_open(WHITELIST_FILE_PATH, O_RDONLY, 0);
    if (IS_ERR(fp)) {
        app_whitelist = kzalloc(sizeof(char *) * (ARRAY_SIZE(default_boost_apps) + 1), GFP_KERNEL);
        if (!app_whitelist) {
            mutex_unlock(&whitelist_lock);
            return;
        }
        for (i = 0; default_boost_apps[i] != NULL; i++) {
            app_whitelist[i] = kstrdup(default_boost_apps[i], GFP_KERNEL);
            if (!app_whitelist[i]) {
                for (j = 0; j < i; j++)
                    kfree(app_whitelist[j]);
                kfree(app_whitelist);
                app_whitelist = NULL;
                mutex_unlock(&whitelist_lock);
                return;
            }
            whitelist_count++;
        }
        mutex_unlock(&whitelist_lock);
        return;
    }
    
    buffer = kzalloc(MAX_JSON_FILE_SIZE, GFP_KERNEL);
    if (!buffer) {
        filp_close(fp, NULL);
        mutex_unlock(&whitelist_lock);
        return;
    }
    
    len = kernel_read(fp, buffer, MAX_JSON_FILE_SIZE - 1, &pos);
    filp_close(fp, NULL);
    
    if (len <= 0) {
        kfree(buffer);
        app_whitelist = kzalloc(sizeof(char *) * (ARRAY_SIZE(default_boost_apps) + 1), GFP_KERNEL);
        if (!app_whitelist) {
            mutex_unlock(&whitelist_lock);
            return;
        }
        for (i = 0; default_boost_apps[i] != NULL; i++) {
            app_whitelist[i] = kstrdup(default_boost_apps[i], GFP_KERNEL);
            if (!app_whitelist[i]) {
                for (j = 0; j < i; j++)
                    kfree(app_whitelist[j]);
                kfree(app_whitelist);
                app_whitelist = NULL;
                mutex_unlock(&whitelist_lock);
                return;
            }
            whitelist_count++;
        }
        mutex_unlock(&whitelist_lock);
        return;
    }
    
    buffer[len] = '\0';
    line = buffer;
    
    app_whitelist = kzalloc(sizeof(char *) * MAX_WHITELIST_APPS, GFP_KERNEL);
    if (!app_whitelist) {
        kfree(buffer);
        mutex_unlock(&whitelist_lock);
        return;
    }
    
    whitelist_count = 0;
    
    while (*line) {
        while (*line && (*line == ' ' || *line == '\t' || *line == '\n' ||
                        *line == '\r' || *line == '"')) {
            line++;
        }
        
        if (!*line)
            break;
        
        if (*line == '[') {
            array_depth++;
            line++;
            continue;
        } else if (*line == ']') {
            array_depth--;
            line++;
            continue;
        } else if (*line == ',') {
            line++;
            continue;
        }
        
        if (array_depth == 1) {
            end = line;
            while (*end && *end != ' ' && *end != '\t' && *end != '\n' &&
                   *end != '\r' && *end != '[' && *end != ']' &&
                   *end != '"' && *end != ',') {
                end++;
            }
            
            if (end > line) {
                int word_len = end - line;
                if (word_len > 0) {
                    char word[32];
                    if (word_len < sizeof(word)) {
                        strncpy(word, line, word_len);
                        word[word_len] = '\0';
                        
                        if (strcmp(word, "dynamic") == 0) {
                            current_mode = MODE_WHITELIST;
                            mode_found = 1;
                        } else if (strcmp(word, "whitelist") == 0) {
                            current_mode = MODE_WHITELIST;
                            mode_found = 1;
                        }
                    }
                }
            }
            line = end;
        } else if (array_depth == 2 && whitelist_count < MAX_WHITELIST_APPS) {
            end = line;
            while (*end && *end != ' ' && *end != '\t' && *end != '\n' &&
                   *end != '\r' && *end != '[' && *end != ']' &&
                   *end != '"' && *end != ',') {
                end++;
            }
            
            if (end > line) {
                int app_len = end - line;
                if (app_len > 0 && app_len < MAX_APP_NAME_LEN) {
                    app_whitelist[whitelist_count] = kzalloc(app_len + 1, GFP_KERNEL);
                    if (app_whitelist[whitelist_count]) {
                        strncpy(app_whitelist[whitelist_count], line, app_len);
                        app_whitelist[whitelist_count][app_len] = '\0';
                        if (strlen(app_whitelist[whitelist_count]) > 0) {
                            whitelist_count++;
                        } else {
                            kfree(app_whitelist[whitelist_count]);
                        }
                    }
                }
            }
            line = end;
        } else {
            line++;
        }
    }
    
    if (!mode_found) {
        current_mode = MODE_WHITELIST;
    }
    
    if (whitelist_count == 0) {
        for (i = 0; default_boost_apps[i] != NULL; i++) {
            app_whitelist[i] = kstrdup(default_boost_apps[i], GFP_KERNEL);
            if (!app_whitelist[i]) {
                for (j = 0; j < i; j++)
                    kfree(app_whitelist[j]);
                kfree(app_whitelist);
                app_whitelist = NULL;
                kfree(buffer);
                mutex_unlock(&whitelist_lock);
                return;
            }
            whitelist_count++;
        }
    }
    
    kfree(buffer);
    mutex_unlock(&whitelist_lock);
}

static void free_whitelist(void)
{
    int i;
    if (!app_whitelist)
        return;
    for (i = 0; i < whitelist_count; i++) {
        if (app_whitelist[i])
            kfree(app_whitelist[i]);
    }
    kfree(app_whitelist);
    app_whitelist = NULL;
    whitelist_count = 0;
}

static unsigned long get_system_power_uw_simple(void)
{
    unsigned long power = 0;
    int cpu;
    unsigned int freq, load;
    unsigned long coeff;
    struct cpufreq_policy *policy;
    for_each_online_cpu(cpu) {
        freq = 0;
#ifdef CONFIG_CPU_FREQ
        policy = cpufreq_cpu_get(cpu);
        if (policy) {
            freq = policy->cur;
            cpufreq_cpu_put(policy);
        }
#endif
        load = get_cpu_load(cpu);
        coeff = cpumask_test_cpu(cpu, &big_mask) ? 8 : 3;
        if (freq == 0)
            freq = LITTLE_CORE_MIN_KHZ;
        power += (freq / 1000000) * load * coeff;
    }
    return power * 1000;
}

static void update_power_statistics(void)
{
    unsigned long current_power = get_system_power_uw_simple();
    unsigned long sum = 0;
    int i;
    if (!screen_on) {
        return;
    }
    power_samples[power_sample_index] = current_power;
    power_sample_index = (power_sample_index + 1) % ARRAY_SIZE(power_samples);
    if (power_sample_count < ARRAY_SIZE(power_samples)) {
        power_sample_count++;
    }
    for (i = 0; i < power_sample_count; i++) {
        sum += power_samples[i];
    }
    if (power_sample_count)
        avg_power_uw = sum / power_sample_count;
    if (current_power > max_power_uw) {
        max_power_uw = current_power;
    }
    last_power_uw = current_power;
    if (avg_power_uw > POWER_THRESHOLD_HIGH * 1000) {
        if (!full_power_mode && screen_on) {
            full_power_mode = true;
            queue_work(fa_wq, &full_power_work);
        }
    } else if (avg_power_uw < POWER_THRESHOLD_MID * 1000) {
        if (full_power_mode) {
            full_power_mode = false;
        }
    }
    if (avg_power_uw > POWER_THRESHOLD_CRITICAL * 1000) {
        if (!power_emergency_mode && screen_on) {
            power_emergency_mode = true;
            emergency_power_throttle();
        }
    } else if (avg_power_uw < POWER_THRESHOLD_HIGH * 1000) {
        if (power_emergency_mode) {
            power_emergency_mode = false;
        }
    }
}

static void emergency_power_throttle(void)
{
    struct task_struct *p;
    set_all_little_core_freq(LOCK_FREQ_KHZ);
    set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(LOCK_FREQ_KHZ);
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        set_user_nice(p, 19);
        set_cpus_allowed_ptr(p, &little_mask);
    }
    rcu_read_unlock();
}

static int read_temperature_from_file(const char *path)
{
    struct file *fp = NULL;
    loff_t pos = 0;
    char buffer[32];
    ssize_t len;
    int temp = 0;
    
    fp = filp_open(path, O_RDONLY | O_NONBLOCK, 0);
    if (IS_ERR(fp)) {
        return -1;
    }
    
    len = kernel_read(fp, buffer, sizeof(buffer) - 1, &pos);
    filp_close(fp, NULL);
    
    if (len <= 0) {
        return -1;
    }
    
    buffer[len] = '\0';
    if (kstrtoint(buffer, 10, &temp) != 0) {
        return -1;
    }
    
    return temp / 1000;
}

static int read_temperature_from_thermal(void)
{
    int temp = -1;
    const char *thermal_paths[] = {
        "/sys/class/thermal/thermal_zone0/temp",
        "/sys/class/thermal/thermal_zone1/temp",
        "/sys/class/thermal/thermal_zone2/temp",
        "/sys/class/thermal/thermal_zone3/temp",
        "/sys/class/thermal/thermal_zone4/temp",
        "/sys/class/hwmon/hwmon0/temp1_input",
        "/sys/class/hwmon/hwmon1/temp1_input",
        "/sys/devices/virtual/thermal/thermal_zone0/temp",
        NULL
    };
    
    int i;
    for (i = 0; thermal_paths[i] != NULL; i++) {
        temp = read_temperature_from_file(thermal_paths[i]);
        if (temp > 0 && temp < 150) {
            return temp;
        }
    }
    
    return temp;
}

static int get_cpu_temperature(void)
{
    static int last_valid_temp = 25;
    int temp = -1;
    
#ifdef CONFIG_THERMAL
    {
        const char *tz_names[] = {
            "cpu-thermal",
            "cpu_thermal",
            "soc_thermal",
            "therm_est",
            "virtual-thermal",
            "cpu_therm",
            "soc",
            NULL
        };
        
        struct thermal_zone_device *tz = NULL;
        int i;
        
        for (i = 0; tz_names[i] != NULL; i++) {
            tz = thermal_zone_get_zone_by_name(tz_names[i]);
            if (!IS_ERR(tz)) {
                int ret = thermal_zone_get_temp(tz, &temp);
                if (!ret) {
                    temp = temp / 1000;
                    if (temp > 0 && temp < 150) {
                        last_valid_temp = temp;
                        last_temperature = temp;
                        return temp;
                    }
                }
            }
        }
    }
#endif
    
    temp = read_temperature_from_thermal();
    if (temp > 0 && temp < 150) {
        last_valid_temp = temp;
        last_temperature = temp;
        return temp;
    }
    
    last_temperature = last_valid_temp;
    return last_valid_temp;
}

static void check_thermal_status(void)
{
    int temp = get_cpu_temperature();
    if (temp > THERMAL_THRESHOLD) {
        if (!thermal_throttle_mode) {
            thermal_throttle_mode = true;
            apply_thermal_throttle();
        }
    } else if (temp < THERMAL_THRESHOLD - 5) {
        if (thermal_throttle_mode) {
            thermal_throttle_mode = false;
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
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(limit_freq);
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        if (p->static_prio < FA_DEFAULT_NICE) {
            set_user_nice(p, FA_DEFAULT_NICE);
        }
    }
    rcu_read_unlock();
}

static void full_power_work_func(struct work_struct *work)
{
    struct task_struct *p;
    if (!full_power_mode || !screen_on)
        return;
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(BIG_CORE_MAX_FREQ_KHZ);
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
}

static void exit_full_power_mode(void)
{
    if (full_power_mode) {
        full_power_mode = false;
    }
}

static void update_task_info(struct task_struct *task)
{
    struct task_info *info;
    char package_name[MAX_PACKAGE_NAME_LEN];
    bool is_foreground = (task->pid == fg_pid);
    if (!get_package_name_safe(task->pid, package_name, sizeof(package_name))) {
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
        info->is_essential = is_essential_app(package_name);
        info->is_whitelisted = is_whitelisted_app(package_name);
        info->last_boost_jiffies = 0;
        info->is_heavy_task = false;
        info->avg_power_uw = 0;
        info->last_power_check = jiffies;
        info->is_frozen = false;
        info->cluster_type = get_app_cluster_type(package_name);
        spin_lock(&task_list_lock);
        list_add_tail(&info->list, &task_list);
        spin_unlock(&task_list_lock);
    } else {
        info->is_foreground = is_foreground;
        if (strcmp(info->package_name, package_name) != 0) {
            strncpy(info->package_name, package_name, sizeof(info->package_name) - 1);
            info->package_name[sizeof(info->package_name) - 1] = '\0';
            info->is_essential = is_essential_app(package_name);
            info->is_whitelisted = is_whitelisted_app(package_name);
            info->cluster_type = get_app_cluster_type(package_name);
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
            unsigned long cpu_power = (freq / 1000000) * load * 2;
            info->avg_power_uw = cpu_power * 100;
            cpufreq_cpu_put(policy);
        }
        info->last_power_check = now;
    }
}

static void schedule_screen_off_mode(void)
{
    struct task_struct *p;
    struct task_info *info;
    int essential_count = 0;
    int limited_count = 0;
    if (screen_off_processed)
        return;
    online_all_little_cores();
    set_all_little_core_freq(LOCK_FREQ_KHZ);
    set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(LOCK_FREQ_KHZ);
    cancel_delayed_work(&check_work);
    cancel_delayed_work(&power_check_work);
    cancel_delayed_work(&idle_check_work);
    cancel_delayed_work(&pid_detect_work);
    cpumask_copy(&screen_off_mask, &little_mask);
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        if (p->pid <= 100)
            continue;
        info = find_task_info(p->pid);
        if (info && info->is_essential) {
            set_user_nice(p, FA_DEFAULT_NICE);
            set_cpus_allowed_ptr(p, &screen_off_mask);
            essential_count++;
        } else {
            set_user_nice(p, 19);
            set_cpus_allowed_ptr(p, &screen_off_mask);
            if (info)
                info->is_frozen = true;
            limited_count++;
        }
    }
    rcu_read_unlock();
    screen_off_processed = true;
}

static void schedule_screen_on_mode(void)
{
    struct task_struct *p;
    struct task_info *info;
    online_all_little_cores();
    set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
    set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(BIG_CORE_MID_FREQ_KHZ);
    unfreeze_all_tasks();
    rcu_read_lock();
    for_each_process(p) {
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
        info = find_task_info(p->pid);
        if (info && info->is_essential) {
            set_user_nice(p, FA_DEFAULT_NICE);
            set_cpus_allowed_ptr(p, &little_mask);
        }
    }
    rcu_read_unlock();
    screen_off_processed = false;
    screen_idle_mode = false;
    if (fa_wq) {
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &power_check_work,
                          msecs_to_jiffies(POWER_CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &idle_check_work,
                          msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        queue_delayed_work(fa_wq, &pid_detect_work,
                          msecs_to_jiffies(PID_CHECK_INTERVAL_MS));
    }
}

static void enter_screen_idle_mode(void)
{
    if (!screen_on || screen_idle_mode || screen_off_processed)
        return;
    screen_idle_mode = true;
    set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
    set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(BIG_CORE_IDLE_FREQ_KHZ);
}

static void exit_screen_idle_mode(void)
{
    if (!screen_idle_mode)
        return;
    screen_idle_mode = false;
    set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
    set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
    if (pc_set_persistent_limit_ptr)
        pc_set_persistent_limit_ptr(BIG_CORE_MID_FREQ_KHZ);
}

static bool pid_detect_timeout_check(void)
{
    unsigned long now = jiffies;
    unsigned long timeout = msecs_to_jiffies(PID_DETECT_TIMEOUT_MS);
    
    if (time_after(now, pid_detect_start_jiffies + timeout)) {
        return true;
    }
    return false;
}

static void detect_foreground_pid_safe(void)
{
    struct task_struct *p;
    char package_name[MAX_PACKAGE_NAME_LEN];
    pid_t new_fg_pid = 0;
    int i;
    int process_count = 0;
    
    spin_lock(&pid_detect_lock);
    if (pid_detect_in_progress) {
        spin_unlock(&pid_detect_lock);
        return;
    }
    pid_detect_in_progress = true;
    pid_detect_start_jiffies = jiffies;
    spin_unlock(&pid_detect_lock);
    
    rcu_read_lock();
    for_each_process(p) {
        if (pid_detect_timeout_check()) {
            break;
        }
        
        if (process_count++ > MAX_PROCESS_SCAN) {
            break;
        }
        
        if (!p->mm || p->flags & PF_KTHREAD)
            continue;
            
        if (p->pid <= 100)
            continue;
        
        if (!get_package_name_safe(p->pid, package_name, sizeof(package_name)))
            continue;
        
        for (i = 0; foreground_process_patterns[i] != NULL; i++) {
            if (strstr(package_name, foreground_process_patterns[i])) {
                new_fg_pid = p->pid;
                break;
            }
        }
        
        if (new_fg_pid != 0)
            break;
    }
    rcu_read_unlock();
    
    if (new_fg_pid != 0 && new_fg_pid != fg_pid) {
        mutex_lock(&fg_lock);
        fg_pid = new_fg_pid;
        mutex_unlock(&fg_lock);
    }
    
    spin_lock(&pid_detect_lock);
    pid_detect_in_progress = false;
    spin_unlock(&pid_detect_lock);
}

static void schedule_notification_app(struct task_struct *p, struct task_info *info)
{
    set_user_nice(p, 19);
    set_cpus_allowed_ptr(p, &little_mask);
}

static void schedule_whitelist_app(struct task_struct *p, struct task_info *info)
{
    if (!info)
        return;
    
    if (info->cluster_type >= 0) {
        schedule_whitelist_app_by_cluster(p, info, info->cluster_type);
    } else {
        unsigned int big_core_load;
        set_user_nice(p, -20);
        set_cpus_allowed_ptr(p, &big_mask);
        big_core_load = get_big_core_load();
        if (big_core_load > BIG_CORE_LOAD_THRESHOLD) {
            if (big_core_load > ALL_CORE_LOAD_THRESHOLD) {
                set_cpus_allowed_ptr(p, &all_mask);
            }
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
            set_user_nice(p, FA_DEFAULT_NICE);
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

static void adjust_frequencies_with_power(void)
{
    unsigned int big_load = get_big_core_load();
    unsigned int little_load = get_cpu_load(LITTLE_START);
    if (!screen_on) {
        return;
    }
    if (screen_idle_mode) {
        set_all_little_core_freq(LITTLE_CORE_MIN_KHZ);
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
    } else {
        set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
        set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
    }
}

static void pid_detect_work_func(struct work_struct *work)
{
    detect_foreground_pid_safe();
    
    if (fa_wq) {
        unsigned long interval = msecs_to_jiffies(PID_CHECK_INTERVAL_MS);
        queue_delayed_work(fa_wq, &pid_detect_work, interval);
    }
}

static void idle_check_work_func(struct work_struct *work)
{
    unsigned long now = jiffies;
    unsigned long idle_timeout = msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS);
    if (screen_on && !screen_idle_mode && !screen_off_processed) {
        if (time_after(now, last_touch_jiffies + idle_timeout)) {
            enter_screen_idle_mode();
        } else {
            if (fa_wq)
                queue_delayed_work(fa_wq, &idle_check_work,
                                  msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        }
    }
}

static void check_work_func(struct work_struct *work)
{
    struct task_info *info, *tmp;
    struct task_struct *task;
    
    rcu_read_lock();
    for_each_process(task) {
        if (!task->mm || task->flags & PF_KTHREAD)
            continue;
        update_task_info(task);
        info = find_task_info(task->pid);
        if (!info)
            continue;
        
        analyze_application_behavior(task, info);
        
        if (info->is_essential) {
            schedule_notification_app(task, info);
        } else if (info->is_whitelisted) {
            schedule_whitelist_app(task, info);
        } else {
            schedule_normal_app_enhanced(task, info);
        }
    }
    rcu_read_unlock();
    
    adjust_frequencies_with_power();
    
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
    
    if (fa_wq)
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
}

static void boost_work_func(struct work_struct *work)
{
    struct task_info *info;
    int cluster_type;
    
    if (fg_pid == 0)
        return;
    if (screen_idle_mode) {
        exit_screen_idle_mode();
    }
    info = find_task_info(fg_pid);
    if (info) {
        info->last_boost_jiffies = jiffies;
        if (info->is_whitelisted) {
            cluster_type = info->cluster_type;
            if (cluster_type == CLUSTER_TYPE_LITTLE) {
                set_all_big_core_freq(BIG_CORE_IDLE_FREQ_KHZ);
                set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
                if (pc_set_persistent_limit_ptr)
                    pc_set_persistent_limit_ptr(BIG_CORE_IDLE_FREQ_KHZ);
            } else if (cluster_type == CLUSTER_TYPE_BIG) {
                set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
                if (pc_set_persistent_limit_ptr)
                    pc_set_persistent_limit_ptr(BIG_CORE_BOOST_HZ_KHZ);
            } else if (cluster_type == CLUSTER_TYPE_ALL) {
                set_all_big_core_freq(BIG_CORE_MAX_FREQ_KHZ);
                set_all_little_core_freq(LITTLE_CORE_MAX_KHZ);
                if (pc_set_persistent_limit_ptr)
                    pc_set_persistent_limit_ptr(BIG_CORE_MAX_FREQ_KHZ);
            } else {
                set_all_big_core_freq(BIG_CORE_BOOST_HZ_KHZ);
                if (pc_set_persistent_limit_ptr)
                    pc_set_persistent_limit_ptr(BIG_CORE_BOOST_HZ_KHZ);
            }
        } else {
            set_all_big_core_freq(BIG_CORE_MID_FREQ_KHZ);
            if (pc_set_persistent_limit_ptr)
                pc_set_persistent_limit_ptr(BIG_CORE_MID_FREQ_KHZ);
        }
    }
}

static void screen_off_work_func(struct work_struct *work)
{
    if (!screen_on && !screen_off_processed) {
        schedule_screen_off_mode();
    }
}

static void power_check_work_func(struct work_struct *work)
{
    if (screen_on) {
        update_power_statistics();
        if (full_power_mode && avg_power_uw < POWER_THRESHOLD_MID * 1000) {
            exit_full_power_mode();
        }
        if (fa_wq)
            queue_delayed_work(fa_wq, &power_check_work,
                              msecs_to_jiffies(POWER_CHECK_INTERVAL_MS));
    }
}

static void thermal_check_work_func(struct work_struct *work)
{
    check_thermal_status();
    if (fa_wq)
        queue_delayed_work(fa_wq, &thermal_check_work,
                          msecs_to_jiffies(5000));
}

static void boot_complete_work_func(struct work_struct *work)
{
    boot_complete = true;
    load_config_from_file();
    if (!input_handler_registered && fa_wq) {
        int rc = input_register_handler(&fa_input_handler);
        if (rc == 0) {
            input_handler_registered = true;
        }
    }
    if (screen_on && fa_wq) {
        queue_delayed_work(fa_wq, &check_work, msecs_to_jiffies(CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &power_check_work, msecs_to_jiffies(POWER_CHECK_INTERVAL_MS));
        queue_delayed_work(fa_wq, &idle_check_work, msecs_to_jiffies(IDLE_NO_TOUCH_DELAY_MS));
        queue_delayed_work(fa_wq, &pid_detect_work, msecs_to_jiffies(PID_CHECK_INTERVAL_MS));
    }
}

static void delayed_save_profiles_work_func(struct work_struct *work)
{
    save_app_profiles_to_buffer();
    if (fa_wq)
        queue_delayed_work(fa_wq, &delayed_save_profiles_work,
                          msecs_to_jiffies(60000));
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
            if (fa_wq)
                queue_work(fa_wq, &boost_work);
        }
    } else {
        if (screen_on) {
            screen_on = false;
            screen_off_jiffies = jiffies;
            cancel_delayed_work(&check_work);
            cancel_delayed_work(&power_check_work);
            cancel_delayed_work(&idle_check_work);
            cancel_delayed_work(&pid_detect_work);
            cancel_delayed_work(&screen_off_work);
            if (fa_wq)
                queue_delayed_work(fa_wq, &screen_off_work,
                                  msecs_to_jiffies(SCREEN_OFF_DELAY_MS));
        }
    }
    return NOTIFY_OK;
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
    if (!screen_on || !fa_wq)
        return;
    if (type == EV_ABS || type == EV_KEY || type == EV_SYN) {
        last_touch_jiffies = jiffies;
        if (screen_idle_mode) {
            screen_idle_mode = false;
            exit_screen_idle_mode();
        }
        if (!work_pending(&boost_work))
            queue_work(fa_wq, &boost_work);
        if (!delayed_work_pending(&check_work))
            mod_delayed_work(fa_wq, &check_work, msecs_to_jiffies(50));
    }
}

static int detect_app_category(const char *package_name)
{
    if (!package_name)
        return APP_CATEGORY_BACKGROUND;
    if (strstr(package_name, "system") ||
        strstr(package_name, "android.") ||
        strstr(package_name, "com.android.")) {
        return APP_CATEGORY_SYSTEM;
    }
    if (strstr(package_name, ".game") ||
        strstr(package_name, "game.") ||
        strstr(package_name, "com.gameloft") ||
        strstr(package_name, "com.miHoYo") ||
        strstr(package_name, "com.tencent.tmgp")) {
        return APP_CATEGORY_GAME;
    }
    if (strstr(package_name, "video") ||
        strstr(package_name, "player") ||
        strstr(package_name, "youtube") ||
        strstr(package_name, "bilibili") ||
        strstr(package_name, "netflix")) {
        return APP_CATEGORY_VIDEO;
    }
    if (strstr(package_name, "browser") ||
        strstr(package_name, "chrome") ||
        strstr(package_name, "firefox") ||
        strstr(package_name, "webview")) {
        return APP_CATEGORY_BROWSER;
    }
    if (strstr(package_name, "facebook") ||
        strstr(package_name, "twitter") ||
        strstr(package_name, "instagram") ||
        strstr(package_name, "whatsapp") ||
        strstr(package_name, "wechat") ||
        strstr(package_name, "qq")) {
        return APP_CATEGORY_SOCIAL;
    }
    return APP_CATEGORY_INTERACTIVE;
}

static void analyze_application_behavior(struct task_struct *p, struct task_info *info)
{
    struct app_profile *profile;
    bool found = false;
    unsigned long now = jiffies;
    unsigned long runtime;
    unsigned int cpu_usage;
    spin_lock(&app_profiles_lock);
    list_for_each_entry(profile, &app_profiles, list) {
        if (strcmp(profile->package_name, info->package_name) == 0) {
            found = true;
            break;
        }
    }
    if (!found) {
        profile = kzalloc(sizeof(*profile), GFP_ATOMIC);
        if (!profile) {
            spin_unlock(&app_profiles_lock);
            return;
        }
        strncpy(profile->package_name, info->package_name, MAX_PACKAGE_NAME_LEN - 1);
        profile->category = detect_app_category(info->package_name);
        profile->prefers_big_cores = false;
        profile->prefers_frequency = false;
        profile->avg_cpu_usage = 0;
        profile->avg_wakeups = 0;
        profile->total_runtime = 0;
        profile->cluster_type = info->cluster_type;
        list_add_tail(&profile->list, &app_profiles);
    } else {
        runtime = jiffies_to_msecs(now - info->last_boost_jiffies);
        if (runtime > 0) {
            cpu_usage = get_cpu_load(task_cpu(p));
            if (profile->avg_cpu_usage == 0) {
                profile->avg_cpu_usage = cpu_usage;
            } else {
                profile->avg_cpu_usage = (profile->avg_cpu_usage * 7 + cpu_usage * 3) / 10;
            }
            profile->total_runtime += runtime;
            if (profile->avg_cpu_usage > 40) {
                profile->prefers_big_cores = true;
            }
            if (profile->avg_cpu_usage > 70 || profile->category == APP_CATEGORY_GAME || profile->category == APP_CATEGORY_VIDEO) {
                profile->prefers_frequency = true;
            }
        }
        profile->last_update = now;
    }
    spin_unlock(&app_profiles_lock);
}

static struct app_profile *find_app_profile(const char *package_name)
{
    struct app_profile *profile;
    spin_lock(&app_profiles_lock);
    list_for_each_entry(profile, &app_profiles, list) {
        if (strcmp(profile->package_name, package_name) == 0) {
            spin_unlock(&app_profiles_lock);
            return profile;
        }
    }
    spin_unlock(&app_profiles_lock);
    return NULL;
}

static void save_app_profiles_to_buffer(void)
{
    struct app_profile *profile;
    char *buffer;
    char *ptr;
    size_t size = 0;
    size_t offset = 0;
    
    mutex_lock(&profile_data_lock);
    
    spin_lock(&app_profiles_lock);
    
    list_for_each_entry(profile, &app_profiles, list) {
        if (profile->total_runtime > 0) {
            size += snprintf(NULL, 0, "%s:%d:%d:%d:%u:%lu:%d\n",
                           profile->package_name,
                           profile->category,
                           profile->prefers_big_cores ? 1 : 0,
                           profile->prefers_frequency ? 1 : 0,
                           profile->avg_cpu_usage,
                           profile->total_runtime,
                           profile->cluster_type);
        }
    }
    
    spin_unlock(&app_profiles_lock);
    
    if (size == 0) {
        mutex_unlock(&profile_data_lock);
        return;
    }
    
    size += 1;
    
    if (size > MAX_PROFILE_DATA_SIZE) {
        size = MAX_PROFILE_DATA_SIZE;
    }
    
    buffer = vmalloc(size);
    if (!buffer) {
        mutex_unlock(&profile_data_lock);
        return;
    }
    
    ptr = buffer;
    
    spin_lock(&app_profiles_lock);
    
    list_for_each_entry(profile, &app_profiles, list) {
        if (profile->total_runtime > 0) {
            int written = snprintf(ptr, size - offset,
                                 "%s:%d:%d:%d:%u:%lu:%d\n",
                                 profile->package_name,
                                 profile->category,
                                 profile->prefers_big_cores ? 1 : 0,
                                 profile->prefers_frequency ? 1 : 0,
                                 profile->avg_cpu_usage,
                                 profile->total_runtime,
                                 profile->cluster_type);
            
            if (written <= 0 || offset + written >= size - 1)
                break;
            
            ptr += written;
            offset += written;
        }
    }
    
    spin_unlock(&app_profiles_lock);
    
    buffer[offset] = '\0';
    
    if (profile_data_buffer) {
        vfree(profile_data_buffer);
    }
    
    profile_data_buffer = buffer;
    profile_data_size = offset;
    
    mutex_unlock(&profile_data_lock);
}

static char *custom_strtok_r(char *str, const char *delim, char **saveptr)
{
    char *token_start, *token_end;
    
    if (str != NULL) {
        *saveptr = str;
    }
    
    if (*saveptr == NULL || **saveptr == '\0') {
        return NULL;
    }
    
    token_start = *saveptr;
    
    token_end = strpbrk(token_start, delim);
    
    if (token_end != NULL) {
        *token_end = '\0';
        *saveptr = token_end + 1;
    } else {
        *saveptr = NULL;
    }
    
    return token_start;
}

static void load_app_profiles_from_buffer(void)
{
    char *buffer;
    char *line;
    char *saveptr;
    
    mutex_lock(&profile_data_lock);
    
    if (!profile_data_buffer || profile_data_size == 0) {
        mutex_unlock(&profile_data_lock);
        return;
    }
    
    buffer = vmalloc(profile_data_size + 1);
    if (!buffer) {
        mutex_unlock(&profile_data_lock);
        return;
    }
    
    memcpy(buffer, profile_data_buffer, profile_data_size);
    buffer[profile_data_size] = '\0';
    
    mutex_unlock(&profile_data_lock);
    
    spin_lock(&app_profiles_lock);
    
    line = custom_strtok_r(buffer, "\n", &saveptr);
    while (line) {
        char package_name[MAX_PACKAGE_NAME_LEN];
        int category;
        int prefers_big_cores;
        int prefers_frequency;
        unsigned int avg_cpu_usage;
        unsigned long total_runtime;
        int cluster_type;
        
        int fields = sscanf(line, "%255[^:]:%d:%d:%d:%u:%lu:%d",
                          package_name, &category, &prefers_big_cores,
                          &prefers_frequency, &avg_cpu_usage, &total_runtime,
                          &cluster_type);
        
        if (fields == 7) {
            struct app_profile *profile = find_app_profile(package_name);
            if (!profile) {
                profile = kzalloc(sizeof(*profile), GFP_ATOMIC);
                if (profile) {
                    strncpy(profile->package_name, package_name, MAX_PACKAGE_NAME_LEN - 1);
                    profile->package_name[MAX_PACKAGE_NAME_LEN - 1] = '\0';
                    profile->category = category;
                    profile->prefers_big_cores = (prefers_big_cores != 0);
                    profile->prefers_frequency = (prefers_frequency != 0);
                    profile->avg_cpu_usage = avg_cpu_usage;
                    profile->total_runtime = total_runtime;
                    profile->cluster_type = cluster_type;
                    profile->avg_wakeups = 0;
                    profile->last_update = jiffies;
                    INIT_LIST_HEAD(&profile->list);
                    list_add_tail(&profile->list, &app_profiles);
                }
            } else {
                profile->category = category;
                profile->prefers_big_cores = (prefers_big_cores != 0);
                profile->prefers_frequency = (prefers_frequency != 0);
                profile->avg_cpu_usage = (profile->avg_cpu_usage + avg_cpu_usage) / 2;
                profile->total_runtime += total_runtime;
                if (cluster_type >= 0)
                    profile->cluster_type = cluster_type;
            }
        } else if (fields == 6) {
            struct app_profile *profile = find_app_profile(package_name);
            if (!profile) {
                profile = kzalloc(sizeof(*profile), GFP_ATOMIC);
                if (profile) {
                    strncpy(profile->package_name, package_name, MAX_PACKAGE_NAME_LEN - 1);
                    profile->package_name[MAX_PACKAGE_NAME_LEN - 1] = '\0';
                    profile->category = category;
                    profile->prefers_big_cores = (prefers_big_cores != 0);
                    profile->prefers_frequency = (prefers_frequency != 0);
                    profile->avg_cpu_usage = avg_cpu_usage;
                    profile->total_runtime = total_runtime;
                    profile->cluster_type = -1;
                    profile->avg_wakeups = 0;
                    profile->last_update = jiffies;
                    INIT_LIST_HEAD(&profile->list);
                    list_add_tail(&profile->list, &app_profiles);
                }
            } else {
                profile->category = category;
                profile->prefers_big_cores = (prefers_big_cores != 0);
                profile->prefers_frequency = (prefers_frequency != 0);
                profile->avg_cpu_usage = (profile->avg_cpu_usage + avg_cpu_usage) / 2;
                profile->total_runtime += total_runtime;
            }
        }
        
        line = custom_strtok_r(NULL, "\n", &saveptr);
    }
    
    spin_unlock(&app_profiles_lock);
    
    vfree(buffer);
}

static ssize_t app_profiles_data_show(struct kobject *k, struct kobj_attribute *a, char *buf)
{
    ssize_t len = 0;
    
    mutex_lock(&profile_data_lock);
    
    if (!profile_data_buffer || profile_data_size == 0) {
        mutex_unlock(&profile_data_lock);
        return sprintf(buf, "No profile data\n");
    }
    
    if (profile_data_size > PAGE_SIZE - 1) {
        memcpy(buf, profile_data_buffer, PAGE_SIZE - 1);
        buf[PAGE_SIZE - 1] = '\0';
        len = PAGE_SIZE - 1;
    } else {
        memcpy(buf, profile_data_buffer, profile_data_size);
        buf[profile_data_size] = '\0';
        len = profile_data_size;
    }
    
    mutex_unlock(&profile_data_lock);
    
    return len;
}

static ssize_t app_profiles_data_store(struct kobject *k, struct kobj_attribute *a,
                                      const char *buf, size_t count)
{
    char *buffer;
    
    if (count > MAX_PROFILE_DATA_SIZE)
        return -EINVAL;
    
    buffer = vmalloc(count + 1);
    if (!buffer)
        return -ENOMEM;
    
    memcpy(buffer, buf, count);
    buffer[count] = '\0';
    
    mutex_lock(&profile_data_lock);
    
    if (profile_data_buffer) {
        vfree(profile_data_buffer);
    }
    
    profile_data_buffer = buffer;
    profile_data_size = count;
    
    mutex_unlock(&profile_data_lock);
    
    load_app_profiles_from_buffer();
    
    return count;
}

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
        if (screen_on && fa_wq) {
            queue_work(fa_wq, &boost_work);
        }
        mutex_unlock(&fg_lock);
    }
    return count;
}

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
    len += sprintf(buf + len, "Screen State: %s\n",
                   screen_on ? "On" : "Off");
    len += sprintf(buf + len, "Screen Off Processed: %s\n",
                   screen_off_processed ? "Yes" : "No");
    len += sprintf(buf + len, "Screen Idle Mode: %s\n",
                   screen_idle_mode ? "Yes" : "No");
    len += sprintf(buf + len, "Scheduler Mode: Whitelist\n");
    len += sprintf(buf + len, "Cluster Scheduling: Enabled\n");
    return len;
}

static ssize_t power_monitor_store(struct kobject *k, struct kobj_attribute *a,
                                   const char *buf, size_t count)
{
    return count;
}

static ssize_t cluster_scheduling_show(struct kobject *k, struct kobj_attribute *a, char *buf)
{
    int len = 0;
    struct app_profile *profile;
    int app_count = 0;
    
    len += sprintf(buf + len, "Cluster Scheduling Status:\n");
    len += sprintf(buf + len, "LITTLE Cluster (0-3): Applications that prefer efficiency\n");
    len += sprintf(buf + len, "BIG Cluster (4-7): Performance applications\n");
    len += sprintf(buf + len, "ALL Cluster (0-7): Games and heavy applications\n\n");
    
    spin_lock(&app_profiles_lock);
    list_for_each_entry(profile, &app_profiles, list) {
        if (app_count < 30 && profile->cluster_type >= 0) {
            const char *cluster_name;
            switch (profile->cluster_type) {
                case CLUSTER_TYPE_LITTLE:
                    cluster_name = "LITTLE";
                    break;
                case CLUSTER_TYPE_BIG:
                    cluster_name = "BIG";
                    break;
                case CLUSTER_TYPE_ALL:
                    cluster_name = "ALL";
                    break;
                default:
                    cluster_name = "UNKNOWN";
                    break;
            }
            len += sprintf(buf + len, "%s -> %s cluster\n", 
                          profile->package_name, cluster_name);
            app_count++;
        }
    }
    spin_unlock(&app_profiles_lock);
    
    if (app_count == 0) {
        len += sprintf(buf + len, "No cluster assignments found\n");
    }
    
    return len;
}

static ssize_t cluster_scheduling_store(struct kobject *k, struct kobj_attribute *a,
                                       const char *buf, size_t count)
{
    char command[64];
    char app_name[256];
    int cluster_type;
    
    if (sscanf(buf, "%63s %255s %d", command, app_name, &cluster_type) == 3) {
        if (strcmp(command, "set_cluster") == 0) {
            if (cluster_type >= CLUSTER_TYPE_LITTLE && cluster_type <= CLUSTER_TYPE_ALL) {
                struct app_profile *profile = find_app_profile(app_name);
                if (!profile) {
                    profile = kzalloc(sizeof(*profile), GFP_KERNEL);
                    if (profile) {
                        strncpy(profile->package_name, app_name, MAX_PACKAGE_NAME_LEN - 1);
                        profile->package_name[MAX_PACKAGE_NAME_LEN - 1] = '\0';
                        profile->category = detect_app_category(app_name);
                        profile->cluster_type = cluster_type;
                        profile->prefers_big_cores = (cluster_type == CLUSTER_TYPE_BIG || cluster_type == CLUSTER_TYPE_ALL);
                        profile->prefers_frequency = (cluster_type == CLUSTER_TYPE_ALL);
                        profile->avg_cpu_usage = 0;
                        profile->avg_wakeups = 0;
                        profile->total_runtime = 0;
                        profile->last_update = jiffies;
                        INIT_LIST_HEAD(&profile->list);
                        spin_lock(&app_profiles_lock);
                        list_add_tail(&profile->list, &app_profiles);
                        spin_unlock(&app_profiles_lock);
                    }
                } else {
                    profile->cluster_type = cluster_type;
                }
            }
        }
    }
    return count;
}

static ssize_t power_save_show(struct kobject *k, struct kobj_attribute *a, char *buf)
{
    return sprintf(buf, "%d\n", aggressive_power_save ? 1 : 0);
}

static ssize_t power_save_store(struct kobject *k, struct kobj_attribute *a,
                                const char *buf, size_t count)
{
    int value;
    if (kstrtoint(buf, 10, &value) == 0) {
        aggressive_power_save = (value != 0);
        if (aggressive_power_save) {
            dynamic_load_threshold = LOAD_THRESHOLD_HIGH;
            dynamic_power_threshold = POWER_THRESHOLD_LOW;
        } else {
            dynamic_load_threshold = LOAD_THRESHOLD_MID;
            dynamic_power_threshold = POWER_THRESHOLD_MID;
        }
    }
    return count;
}

static struct kobj_attribute fg_attr = __ATTR(fg_pid, 0644, fg_pid_show, fg_pid_store);
static struct kobj_attribute power_attr = __ATTR(power_monitor, 0644, power_monitor_show, power_monitor_store);
static struct kobj_attribute cluster_scheduling_attr = __ATTR(cluster_scheduling, 0644, cluster_scheduling_show, cluster_scheduling_store);
static struct kobj_attribute app_profiles_data_attr = __ATTR(app_profiles_data, 0644, app_profiles_data_show, app_profiles_data_store);
static struct kobj_attribute power_save_attr = __ATTR(power_save, 0644, power_save_show, power_save_store);

static int __init fa_init(void)
{
    int rc;
    pc_set_persistent_limit_ptr = (pc_set_persistent_limit_func)
        kallsyms_lookup_name("pc_set_persistent_limit");
    init_masks();
    spin_lock_init(&task_list_lock);
    INIT_LIST_HEAD(&task_list);
    INIT_LIST_HEAD(&app_profiles);
    mutex_init(&profile_data_lock);
    spin_lock_init(&pid_detect_lock);
    fa_wq = alloc_workqueue("frame_aware_wq", WQ_FREEZABLE | WQ_MEM_RECLAIM | WQ_UNBOUND, 1);
    if (!fa_wq) {
        return -ENOMEM;
    }
    INIT_DELAYED_WORK(&check_work, check_work_func);
    INIT_DELAYED_WORK(&screen_off_work, screen_off_work_func);
    INIT_WORK(&boost_work, boost_work_func);
    INIT_DELAYED_WORK(&boot_complete_work, boot_complete_work_func);
    INIT_DELAYED_WORK(&power_check_work, power_check_work_func);
    INIT_DELAYED_WORK(&thermal_check_work, thermal_check_work_func);
    INIT_WORK(&full_power_work, full_power_work_func);
    INIT_DELAYED_WORK(&idle_check_work, idle_check_work_func);
    INIT_DELAYED_WORK(&delayed_save_profiles_work, delayed_save_profiles_work_func);
    INIT_DELAYED_WORK(&pid_detect_work, pid_detect_work_func);
    rc = fb_register_client(&fb_notifier);
    fa_kobj = kobject_create_and_add("frame_aware", kernel_kobj);
    if (fa_kobj) {
        sysfs_create_file(fa_kobj, &fg_attr.attr);
        sysfs_create_file(fa_kobj, &power_attr.attr);
        sysfs_create_file(fa_kobj, &cluster_scheduling_attr.attr);
        sysfs_create_file(fa_kobj, &app_profiles_data_attr.attr);
        sysfs_create_file(fa_kobj, &power_save_attr.attr);
    }
    last_touch_jiffies = jiffies;
    screen_on = true;
    power_check_jiffies = jiffies;
    thermal_check_jiffies = jiffies;
    if (fa_wq) {
        queue_delayed_work(fa_wq, &thermal_check_work, msecs_to_jiffies(5000));
        queue_delayed_work(fa_wq, &boot_complete_work, msecs_to_jiffies(30000));
        queue_delayed_work(fa_wq, &delayed_save_profiles_work, msecs_to_jiffies(30000));
        queue_delayed_work(fa_wq, &pid_detect_work, msecs_to_jiffies(1000));
    }
    return 0;
}

static void __exit fa_exit(void)
{
    struct task_info *info, *tmp;
    struct app_profile *profile, *ptmp;
    cancel_delayed_work_sync(&check_work);
    cancel_delayed_work_sync(&screen_off_work);
    cancel_work_sync(&boost_work);
    cancel_delayed_work_sync(&boot_complete_work);
    cancel_delayed_work_sync(&power_check_work);
    cancel_delayed_work_sync(&thermal_check_work);
    cancel_work_sync(&full_power_work);
    cancel_delayed_work_sync(&idle_check_work);
    cancel_delayed_work_sync(&delayed_save_profiles_work);
    cancel_delayed_work_sync(&pid_detect_work);
    save_app_profiles_to_buffer();
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
    spin_lock(&app_profiles_lock);
    list_for_each_entry_safe(profile, ptmp, &app_profiles, list) {
        list_del(&profile->list);
        kfree(profile);
    }
    spin_unlock(&app_profiles_lock);
    free_whitelist();
    mutex_lock(&profile_data_lock);
    if (profile_data_buffer) {
        vfree(profile_data_buffer);
        profile_data_buffer = NULL;
        profile_data_size = 0;
    }
    mutex_unlock(&profile_data_lock);
    if (input_handler_registered) {
        input_unregister_handler(&fa_input_handler);
        input_handler_registered = false;
    }
    fb_unregister_client(&fb_notifier);
    if (fa_kobj) {
        sysfs_remove_file(fa_kobj, &fg_attr.attr);
        sysfs_remove_file(fa_kobj, &power_attr.attr);
        sysfs_remove_file(fa_kobj, &cluster_scheduling_attr.attr);
        sysfs_remove_file(fa_kobj, &app_profiles_data_attr.attr);
        sysfs_remove_file(fa_kobj, &power_save_attr.attr);
        kobject_put(fa_kobj);
    }
}

module_init(fa_init);
module_exit(fa_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Unfair Power Scheduler - Cluster Aware Version");
MODULE_DESCRIPTION("Android-aware task scheduler with cluster-based scheduling");
