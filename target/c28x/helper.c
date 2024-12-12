#include "qemu/osdep.h"

#include "cpu.h"
#include "exec/exec-all.h"
#include "exec/helper-proto.h"
#include "hw/c28x/boot.h"
#include "hw/core/cpu.h"
#include "qemu/log.h"

static inline void raise_exception(CPUC28XState* env, int index, uintptr_t retaddr);

static inline G_NORETURN void raise_exception(CPUC28XState* env, int index, uintptr_t retaddr) {
    CPUState* cs = env_cpu(env);
    cs->exception_index = index;
    cpu_loop_exit_restore(cs, retaddr);
}

void helper_raise_illegal_instruction(CPUC28XState* env) {
    CPUState* cs = env_cpu(env);

    cs->exception_index = EXCP_DEBUG;
    qemu_log("Illegal instruction\n");
    cpu_dump_state(cs, stderr, 0);
    cpu_loop_exit(cs);
}

bool c28x_cpu_tlb_fill(CPUState* cs, vaddr address, int size, MMUAccessType access_type, int mmu_idx, bool probe,
                       uintptr_t retaddr) {
    int port = 0;

    port = PAGE_READ | PAGE_WRITE | PAGE_EXEC;
    tlb_set_page(cs, address, address, port, mmu_idx, TARGET_PAGE_SIZE);
    return true;
}

void c28x_cpu_do_interrupt(struct CPUState* cs) {
    // TODO!: Figure out how to implement this
}

hwaddr c28x_cpu_get_phys_page_debug(struct CPUState* cs, vaddr addr) { return addr; }

int c28x_cpu_memory_rw_debug(CPUState* cs, vaddr addr, uint8_t* buf, int len, bool is_write) {
    return cpu_memory_rw_debug(cs, addr, buf, len, is_write);
}