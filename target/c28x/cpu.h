#ifndef QEMU_C28X_CPU_H
#define QEMU_C28X_CPU_H

#include "cpu-qom.h"
#include "exec/cpu-defs.h"

#define C28X_EXP   0x100
#define C28X_EXP_S C28X_EXP | 0x30

// C28X registers
// =================
// ACC = AH + AL (Accumulator) / 32-bit
// XAR0 - XAR7 (Auxiliary registers) / Low half as AR0 - AR7 / 32-bit
// DP (Data Pointer) / 16-bit
// IFR (Interrupt Flag Register) / 16-bit
// IER (Interrupt Enable Register) / 16-bit
// DBGIER (Debug Interrupt Enable Register) / 16-bit
// P (Product register) = PH + PL / 32-bit
// PC (Program Counter) / 22-bit
// RPC (Return Program Counter) / 22-bit
// SP (Stack Pointer) / 16-bit
// ST0 - ST1 (Status registers) / 16-bit
// XT = T + TL (Multiplicand register) / 32-bit
// =================
// Total 20 registers
#define C28X_REG_PAGE_SIZE 20
// Register ID, just for reference
#define C28X_REG_ACC    0
#define C28X_REG_XAR0   1
#define C28X_REG_XAR1   2
#define C28X_REG_XAR2   3
#define C28X_REG_XAR3   4
#define C28X_REG_XAR4   5
#define C28X_REG_XAR5   6
#define C28X_REG_XAR6   7
#define C28X_REG_XAR7   8
#define C28X_REG_DP     9
#define C28X_REG_IFR    10
#define C28X_REG_IER    11
#define C28X_REG_DBGIER 12
#define C28X_REG_P      13
#define C28X_REG_PC     14
#define C28X_REG_RPC    15
#define C28X_REG_SP     16
#define C28X_REG_ST0    17
#define C28X_REG_ST1    18
#define C28X_REG_XT     19

#define CPU_RESOLVING_TYPE TYPE_C28X_CPU

// CPU definition
struct C28XCPUDef {
    const char* name;
    size_t core_type;
    size_t series_type;
    size_t clock_speed;
};

static const char c28x_cpu_r_names[C28X_REG_PAGE_SIZE][8] = {"ACC",  "XAR0", "XAR1", "XAR2", "XAR3", "XAR4",   "XAR5",
                                                             "XAR6", "XAR7", "DP",   "IFR",  "IER",  "DBGIER", "P",
                                                             "PC",   "RPC",  "SP",   "ST0",  "ST1",  "XT"};

typedef struct CPUArchState {
    // Status Register
    uint32_t sr;
    uint32_t pc_w;

    // Register File Registers
    uint32_t r[C28X_REG_PAGE_SIZE];

    // interrupt source
    // FIXME: figure out how to write this
} CPUC28XState;

struct ArchCPU {
    // < private >
    CPUState parent_obj;

    // < public >
    // ? In some other implementations, this neg is used
    // ? But in my case, an error is thrown:
    // ? ===========
    // ? !(__builtin_offsetof(struct ArchCPU, env) != sizeof(struct CPUState))': not expecting: offsetof(ArchCPU, env)
    // ? != sizeof(CPUState) CPUNegativeOffsetState neg;
    // ? ===========
    CPUC28XState env;
};

int c28x_print_insn(bfd_vma addr, disassemble_info* info);

// FIXME: The CPU interrupt function is not implemented yet!
// !!!Handle CPU interrupts HERE!!!

// WARNING: error: conflicting types for 'cpu_mmu_index'
// static inline int cpu_mmu_index(CPUC28XState* env, bool ifetch) { return 0; }
#define MMU_CODE_IDX 0
#define MMU_DATA_IDX 1

static inline void cpu_get_tb_cpu_state(CPUC28XState* env, vaddr* pc, vaddr* cs_base, uint32_t* flags) {
    *pc = env->r[C28X_REG_PC];
    *cs_base = 0;
    *flags = 0;
}

void c28x_tcg_init(void);

bool c28x_cpu_tlb_fill(CPUState* cs, vaddr address, int size, MMUAccessType access_type, int mmu_idx, bool probe,
                       uintptr_t retaddr);

// FIXME: The CPU interrupt function is not implemented yet!
void c28x_cpu_do_interrupt(CPUState* cs);
void c28x_cpu_set_int(void* opaque, int irq, int level);

static inline int cpu_interrupts_enabled(CPUC28XState* env) { return 1; }

hwaddr c28x_cpu_get_phys_page_debug(CPUState* cs, vaddr addr);
int c28x_cpu_memory_rw_debug(CPUState* cs, vaddr addr, uint8_t* buf, int len, bool is_write);

void c28x_cpu_synchronize_from_tb(CPUState* cs, const TranslationBlock* tb);

#include "exec/cpu-all.h"

#endif