#ifndef HW_C28X_BOOT_H
#define HW_C28X_BOOT_H

#include "cpu.h"
#include "hw/boards.h"

bool c28x_load_firmware(C28XCPU* cpu, MachineState* ms, MemoryRegion* mr, const char* firmware);

#endif