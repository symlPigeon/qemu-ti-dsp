// osdep.h MUST be on top
#include "qemu/osdep.h"

#include "boot.h"
#include "hw/loader.h"
#include "qemu/datadir.h"
#include "qemu/error-report.h"

bool c28x_load_firmware(C28XCPU* cpu, MachineState* ms, struct MemoryRegion* mr, const char* firmware) {
    printf("[C28X-BOOT] c28x_load_firmware\n");
    g_autofree char* filename = NULL;
    int bytes_loaded;

    // when qemu started, we get the filename specified as bios
    filename = qemu_find_file(QEMU_FILE_TYPE_BIOS, firmware);
    if (filename == NULL) {
        error_report("Cannot find firmware image %s", firmware);
        return false;
    }

    // use built-in func to load the fw into emu memory
    bytes_loaded = load_image_mr(filename, mr);
    if (bytes_loaded < 0) {
        error_report("Unable to load firmware %s into memory!", filename);
        return false;
    }

    printf("[C28X-BOOT] Loaded %d bytes of firmware %s\n", bytes_loaded, filename);
    return true;
}