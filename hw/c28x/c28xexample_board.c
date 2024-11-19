#include "qemu/osdep.h"

#include "boot.h"
#include "c28xexp.h"
#include "hw/boards.h"
#include "hw/sysbus.h"
#include "qapi/error.h"
#include "qemu/units.h"
#include "qom/object.h"

struct C28XExampleBoardMachineState {
    MachineState parent_obj;
    C28XEXPMcuState mcu;
};
typedef struct C28XExampleBoardMachineState C28XExampleBoardMachineState;

struct C28XExampleBoardMachineClass {
    MachineClass parent_class;
};
typedef struct C28XExampleBoardMachineClass C28XExampleBoardMachineClass;

#define TYPE_C28XEXAMPLE_BOARD_BASE_MACHINE MACHINE_TYPE_NAME("c28xexample-board-base")
#define TYPE_C28XEXAMPLE_BOARD_MACHINE      MACHINE_TYPE_NAME("c28xexample-board")

DECLARE_OBJ_CHECKERS(C28XExampleBoardMachineState, C28XExampleBoardMachineClass, C28XEXAMPLE_BOARD_MACHINE,
                     TYPE_C28XEXAMPLE_BOARD_MACHINE)

static void c28xexample_board_init(MachineState* machine) {
    printf("[C28X-EXAMPLE-BOARD] c28xexample_board_init\n");

    // Make a specific MachineState out of the generic MachineState
    C28XExampleBoardMachineState* m_state = C28XEXAMPLE_BOARD_MACHINE(machine);
    // init the MCU
    object_initialize_child(OBJECT(machine), "mcu", &m_state->mcu, TYPE_C28XEXPS_MCU);
    // connect the MCU to the system bus
    sysbus_realize(SYS_BUS_DEVICE(&m_state->mcu), &error_abort);

    printf("[C28X-EXAMPLE-BOARD] Loading firmware\n");

    // load firmware
    if (machine->firmware) {
        if (!c28x_load_firmware(&m_state->mcu.cpu, machine, &m_state->mcu.flash, machine->firmware)) {
            printf("[C28X-EXAMPLE-BOARD] Failed to load firmware\n");
            exit(1);
        }
    }
    printf("[C28X-EXAMPLE-BOARD] c28xexample_board_init DONE!\n");
}

static void c28xexample_board_class_init(ObjectClass* oc, void* data) {
    printf("[C28X-EXAMPLE-BOARD] c28xexample_board_class_init\n");
    // Generic machine class from object
    MachineClass* mc = MACHINE_CLASS(oc);
    mc->desc = "C28X Example Board";
    mc->alias = "c28xexample-board";

    // tell qemu what func is used to init our board
    mc->init = c28xexample_board_init;
    mc->default_cpus = 1;
    mc->min_cpus = mc->default_cpus;
    mc->max_cpus = mc->default_cpus;
    // no media drv
    mc->no_floppy = 1;
    mc->no_cdrom = 1;
    // no threads
    mc->no_parallel = 1;
}

static const TypeInfo c28xexample_board_machine_types[] = {
    {.name = TYPE_C28XEXAMPLE_BOARD_MACHINE,
     // TYPE_MACHINE --- is parent of --> Our machine class
     .parent = TYPE_MACHINE,
     .instance_size = sizeof(C28XExampleBoardMachineState),
     .class_size = sizeof(C28XExampleBoardMachineClass),
     // register our class init func
     .class_init = c28xexample_board_class_init},
};
DEFINE_TYPES(c28xexample_board_machine_types)