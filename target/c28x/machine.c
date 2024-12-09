// qemu/osdep.h **MUST** be included before anything
#include "qemu/osdep.h"

#include "cpu.h"
#include "migration/cpu.h"

const VMStateDescription vms_c28x_cpu = {.name = "cpu",
                                         .version_id = 1,
                                         .minimum_version_id = 1,
                                         .fields = (VMStateField[]){

                                             VMSTATE_UINT32_ARRAY(env.r, C28XCPU, C28X_REG_PAGE_SIZE),

                                             VMSTATE_END_OF_LIST()}};