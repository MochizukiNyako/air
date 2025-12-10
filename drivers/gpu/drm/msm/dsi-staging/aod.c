#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/fs.h>
#include <linux/device.h>
#include <linux/uaccess.h>
#include <linux/mutex.h>

#include "dsi_display.h"
#include "dsi_panel.h"

#define NYAKO_CLASS_NAME "nyako"
#define AOD_NODE_NAME    "aod"

extern struct dsi_display *get_main_display(void);

static struct class *nyako_class;
static struct device *aod_device;
static DEFINE_MUTEX(aod_lock);
static bool aod_enabled;

static ssize_t aod_store(struct device *dev,
                         struct device_attribute *attr,
                         const char *buf, size_t count)
{
    unsigned int val;
    int ret;
    struct dsi_display *display;
    struct dsi_panel *panel;

    ret = kstrtouint(buf, 10, &val);
    if (ret)
        return ret;

    display = get_main_display();
    if (!display || !display->panel)
        return -ENODEV;

    panel = display->panel;

    mutex_lock(&display->display_lock);

    if (val)
        ret = dsi_panel_set_fod_hbm(panel, true);
    else
        ret = dsi_panel_set_fod_hbm(panel, false);

    mutex_unlock(&display->display_lock);

    if (ret)
        return ret;

    aod_enabled = (val != 0);
    return count;
}

static DEVICE_ATTR_WO(aod);

static struct attribute *aod_attrs[] = {
    &dev_attr_aod.attr,
    NULL,
};

static struct attribute_group aod_attr_group = {
    .attrs = aod_attrs,
};

static int __init nyako_aod_init(void)
{
    int ret;

    pr_info("nyako_aod: initializing AOD highlight driver\n");

    nyako_class = class_create(THIS_MODULE, NYAKO_CLASS_NAME);
    if (IS_ERR(nyako_class)) {
        pr_err("nyako_aod: failed to create class\n");
        return PTR_ERR(nyako_class);
    }

    aod_device = device_create(nyako_class, NULL, 0, NULL, AOD_NODE_NAME);
    if (IS_ERR(aod_device)) {
        pr_err("nyako_aod: failed to create device\n");
        ret = PTR_ERR(aod_device);
        goto destroy_class;
    }

    ret = sysfs_create_group(&aod_device->kobj, &aod_attr_group);
    if (ret) {
        pr_err("nyako_aod: failed to create sysfs group\n");
        goto destroy_device;
    }

    pr_info("nyako_aod: initialized successfully at /sys/class/nyako/aod\n");
    return 0;

destroy_device:
    device_destroy(nyako_class, 0);
destroy_class:
    class_destroy(nyako_class);
    return ret;
}

static void __exit nyako_aod_exit(void)
{
    pr_info("nyako_aod: exiting AOD highlight driver\n");

    sysfs_remove_group(&aod_device->kobj, &aod_attr_group);
    device_destroy(nyako_class, 0);
    class_destroy(nyako_class);

    pr_info("nyako_aod: exited\n");
}

module_init(nyako_aod_init);
module_exit(nyako_aod_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Mochizuki_Nyako");
MODULE_DESCRIPTION("K20Pro Local FOD Highlight Driver (AOD sysfs node)");
MODULE_VERSION("1.0");
