#ifndef C28X_CPU_QOM_H
#define C28X_CPU_QOM_H

#include "hw/core/cpu.h"
#include "qom/object.h"

#define TYPE_C28X_CPU            "c28x-cpu"
#define C28X_CPU_TYPE_SUFFIX     "-" TYPE_C28X_CPU
#define C28X_CPU_TYPE_NAME(name) (name C28X_CPU_TYPE_SUFFIX)

OBJECT_DECLARE_CPU_TYPE(C28XCPU, C28XCPUClass, C28X_CPU)

typedef struct C28XCPUDef C28XCPUDef;
struct C28XCPUClass {
    // < private >
    CPUClass parent_class;

    // < public >
    DeviceRealize parent_realize;
    ResettablePhases parent_phases;

    C28XCPUDef* cpu_def;
};

#endif