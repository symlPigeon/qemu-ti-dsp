#include "qemu/osdep.h"

#include "exec/address-spaces.h"
#include "exec/memory.h"
#include "hw/misc/unimp.h"
#include "hw/qdev-properties.h"
#include "hw/sysbus.h"
#include "qapi/error.h"
#include "qemu/module.h"
#include "qemu/units.h"
#include "qom/object.h"
#include "sysemu/sysemu.h"

#include "c28xexp.h"

struct C28XEXPMcuClass {
    // < private >
    SysBusDeviceClass parent_class;

    // < public >
    const char* cpu_type;
    size_t flash_size;
};
typedef struct C28XEXPMcuClass C28XEXPMcuClass;
DECLARE_CLASS_CHECKERS(C28XEXPMcuClass, C28XEXP_MCU, TYPE_C28XEXP_MCU)

// set up device
static void c28xexp_realize(DeviceState* dev, Error** errp) {
    printf("[C28X-EXP] c28xexp_realize\n");
    // create state from generic state and create a class from state
    C28XEXPMcuState* s = C28XEXP_MCU(dev);
    const C28XEXPMcuClass* mc = C28XEXP_MCU_GET_CLASS(dev);

    // C28X CPU <--- C28XEXPMcuState
    object_initialize_child(OBJECT(dev), "cpu", &s->cpu, mc->cpu_type);
    qdev_realize(DEVICE(&s->cpu), NULL, &error_abort);

    // init memory region
    memory_region_init_rom(&s->flash, OBJECT(dev), "flash", mc->flash_size, &error_fatal);

    // set start addr of flash
    // FIXME: modify this later!
    memory_region_add_subregion(get_system_memory(), 0x00000000, &s->flash);
}

static void c28xexp_class_init(ObjectClass* oc, void* data) {
    printf("[C28X-EXP] c28xexp_class_init\n");
    DeviceClass* dc = DEVICE_CLASS(oc);
    // set actual setup func
    dc->realize = c28xexp_realize;
    dc->user_creatable = false;
}

static void c28xexps_class_init(ObjectClass* oc, void* data) {
    printf("[C28X-EXP] c28xexps_class_init\n");
    C28XEXPMcuClass* c28xexp = C28XEXP_MCU_CLASS(oc);

    c28xexp->cpu_type = C28X_CPU_TYPE_NAME("f28335");
    c28xexp->flash_size = 1024 * KiB;
}

static const TypeInfo c28xexp_mcu_types[] = {{
                                                 .name = TYPE_C28XEXPS_MCU,
                                                 .parent = TYPE_C28XEXP_MCU,
                                                 .class_init = c28xexps_class_init,
                                             },
                                             {.name = TYPE_C28XEXP_MCU,
                                              .parent = TYPE_SYS_BUS_DEVICE,
                                              .instance_size = sizeof(C28XEXPMcuState),
                                              .class_size = sizeof(C28XEXPMcuClass),
                                              .class_init = c28xexp_class_init,
                                              .abstract = true}};

DEFINE_TYPES(c28xexp_mcu_types)