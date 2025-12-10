#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/kobject.h>
#include <linux/sysfs.h>
#include <linux/fs.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("Expose /sys/ufs/ufsid showing soc0/serial_number");

#define SERIAL_PATH "/sys/devices/soc0/serial_number"

static struct kobject *ufs_kobj;

static ssize_t ufsid_show(struct kobject *kobj, struct kobj_attribute *attr, char *buf)
{
    struct file *filp;
    ssize_t ret = 0;
    char *tmp;

    tmp = kzalloc(128, GFP_KERNEL);
    if (!tmp)
        return -ENOMEM;

    filp = filp_open(SERIAL_PATH, O_RDONLY, 0);
    if (IS_ERR(filp)) {
        pr_warn("ufsid: failed to open %s\n", SERIAL_PATH);
        kfree(tmp);
        return -ENOENT;
    }

    ret = kernel_read(filp, tmp, 127, &filp->f_pos);
    if (ret >= 0) {
        tmp[ret] = '\0';
        ret = scnprintf(buf, PAGE_SIZE, "%s", tmp);
    }

    filp_close(filp, NULL);
    kfree(tmp);

    return ret;
}

static struct kobj_attribute ufsid_attr = __ATTR_RO(ufsid);

static int __init ufsid_sysfs_init(void)
{
    int ret;

    ufs_kobj = kobject_create_and_add("ufs", kernel_kobj);
    if (!ufs_kobj)
        return -ENOMEM;

    ret = sysfs_create_file(ufs_kobj, &ufsid_attr.attr);
    if (ret)
        pr_err("ufsid: failed to create ufsid attribute\n");
    else
        pr_info("ufsid: /sys/ufs/ufsid created\n");

    return ret;
}

early_initcall(ufsid_sysfs_init);
