#ifndef HW_C28X_C28XEXPC_H
#define HW_C28X_C28XEXPC_H
#include "exec/memory.h"
#include "hw/sysbus.h"
#include "qom/object.h"
#include "target/c28x/cpu.h"

// C28XEXP MCU
#define TYPE_C28XEXP_MCU "c28xexp"
// C28XEXP MCU SoC
#define TYPE_C28XEXPS_MCU "c28xexps"

typedef struct C28XEXPMcuState C28XEXPMcuState;
DECLARE_INSTANCE_CHECKER(C28XEXPMcuState, C28XEXP_MCU, TYPE_C28XEXP_MCU)

struct C28XEXPMcuState {
    // < private >
    SysBusDevice parent_obj;

    // < public >
    C28XCPU cpu;           // C28X CPU logic
    MemoryRegion flash;    // Flash memory
};

#endif