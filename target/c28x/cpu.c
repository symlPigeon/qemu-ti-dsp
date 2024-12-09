// qemu/osdep.h **MUST** be included before anything
#include "qemu/osdep.h"

#include "cpu-qom.h"
#include "disas/dis-asm.h"
#include "exec/address-spaces.h"
#include "exec/exec-all.h"
#include "exec/helper-proto.h"
#include "hw/core/tcg-cpu-ops.h"
#include "qapi/error.h"
#include "qemu/qemu-print.h"
#include "qemu/typedefs.h"

#include "cpu.h"

static C28XCPU* cpu_self;
static bool first_reset = true;

static int c28x_cpu_mmu_index(CPUState* cs, bool ifetch) { return ifetch ? MMU_CODE_IDX : MMU_DATA_IDX; }

static void c28x_cpu_disas_set_info(CPUState* cpu, disassemble_info* info) {
    printf("[C28X-DISAS] c28x_cpu_disas_set_info\n");
    info->mach = bfd_arch_c28x;
}

static void c28x_cpu_init(Object* obj) {
    printf("[C28X-CPU] c28x_cpu_init\n");
    // generic cpu state from object
    C28XCPU* cpu = C28X_CPU(obj);
    CPUC28XState* env = &cpu->env;

    // do some init here
    // env->r[C28X_REG_PC] = 0x3FFFC0; // NOTE: PC should be set to 0x3FFFC0, but set to 0 is easier for debug
    env->r[C28X_REG_SP] = 0x0400;
    env->sr[MOM1MAP_FLAG] = 1;
    env->sr[VMAP_FLAG] = 1;
    env->sr[DBGM_FLAG] = 1;
    env->sr[INTM_FLAG] = 1;
    env->r[C28X_REG_ACC] = 0xf0001111;
};

static void c28x_cpu_realizefn(DeviceState* dev, Error** errp) {
    printf("[C28X-CPU] c28x_cpu_realizefn\n");
    CPUState* cs = CPU(dev);
    cpu_self = C28X_CPU(cs);
    C28XCPUClass* ccc = C28X_CPU_GET_CLASS(dev);

    Error* local_err = NULL;

    cpu_exec_realizefn(cs, &local_err);
    if (local_err != NULL) {
        error_propagate(errp, local_err);
        return;
    }

    qemu_init_vcpu(cs);
    cpu_reset(cs);

    ccc->parent_realize(dev, errp);
}

static void c28x_cpu_reset(Object* dev, ResetType type) {
    CPUState* cs = CPU(dev);
    C28XCPU* cpu = C28X_CPU(cs);
    C28XCPUClass* ccc = C28X_CPU_GET_CLASS(dev);
    CPUC28XState* env = &cpu->env;

    if (ccc->parent_phases.hold) {
        ccc->parent_phases.hold(dev, type);
    }

    if (first_reset) {
        memset(env->r, 0, sizeof(env->r));
        first_reset = false;
    }

    // FIXME: cpu registers are not all zeros on reset!
    // NOTE: set register status here! For example:
    // env->r[C28X_REG_PC] = 0x3FFFC0; // NOTE: PC should be set to 0x3FFFC0, but set to 0 is easier for debug
    env->r[C28X_REG_SP] = 0x0400;
    env->sr[MOM1MAP_FLAG] = 1;
    env->sr[VMAP_FLAG] = 1;
    env->sr[DBGM_FLAG] = 1;
    env->sr[INTM_FLAG] = 1;

    printf("[C28X-CPU] CPU Reset\n");

    // NOTE: set the start addr of exec
    env->r[C28X_REG_PC] = 0x00000000;    // FIXME: C28X PC reset to 0x3FFFC0
}

static ObjectClass* c28x_cpu_class_by_name(const char* cpu_model) {
    ObjectClass* oc;
    printf("[C28X-CPU] c28x_cpu_class_by_name: %s\n", cpu_model);
    oc = object_class_by_name(C28X_CPU_TYPE_NAME("C28XEXPC"));
    return oc;
}

static bool c28x_cpu_has_work(CPUState* cs) {
    C28XCPU* cpu = C28X_CPU(cs);
    CPUC28XState* env = &cpu->env;

    // FIXME: Interrupt is not implemented yet!
    return (cs->interrupt_request & CPU_INTERRUPT_HARD) && cpu_interrupts_enabled(env);
}

// process `-d cpu` parameter
static void c28x_cpu_dump_state(CPUState* cs, FILE* f, int flags) {
    C28XCPU* cpu = C28X_CPU(cs);
    // use env to access emu regs
    CPUC28XState* env = &cpu->env;

    qemu_fprintf(f, "PC:    " TARGET_FMT_lx "\n", env->r[C28X_REG_PC]);
    qemu_fprintf(f, "RPC:   " TARGET_FMT_lx "\n", env->r[C28X_REG_RPC]);
    qemu_fprintf(f, "DP:   " TARGET_FMT_lx "\n", env->r[C28X_REG_DP]);
    qemu_fprintf(f, "SP:    " TARGET_FMT_lx "\n", env->r[C28X_REG_SP]);
    qemu_fprintf(f, "XT:    " TARGET_FMT_lx "\n", env->r[C28X_REG_XT]);
    qemu_fprintf(f, "ACC:   " TARGET_FMT_lx "\n", env->r[C28X_REG_ACC]);
    qemu_fprintf(f, "P:     " TARGET_FMT_lx "\n", env->r[C28X_REG_P]);
    qemu_fprintf(f, "IFR:   " TARGET_FMT_lx "\n", env->r[C28X_REG_IFR]);
    qemu_fprintf(f, "IER:   " TARGET_FMT_lx "\n", env->r[C28X_REG_IER]);
    qemu_fprintf(f, "DBGIER:" TARGET_FMT_lx "\n", env->r[C28X_REG_DBGIER]);

    for (int i = 0; i <= 7; i++) {
        qemu_fprintf(f, "XAR%d:  " TARGET_FMT_lx "\n", i, env->r[C28X_REG_XAR0 + i]);
    }

    qemu_fprintf(f, "\n");
}

static void c28x_cpu_set_pc(CPUState* cs, vaddr value) {
    C28XCPU* cpu = C28X_CPU(cs);
    CPUC28XState* env = &cpu->env;

    env->r[C28X_REG_PC] = value;
    printf("[C28X-CPU] Set PC to " TARGET_FMT_lx "\n", value);
}

static bool c28x_cpu_exec_interrupt(CPUState* cs, int interrupt_request) {
    // TODO: later
    return false;
}

#include "hw/core/sysemu-cpu-ops.h"

static const struct SysemuCPUOps c28x_sysemu_ops = {
    .get_phys_page_debug = c28x_cpu_get_phys_page_debug,
};

static const struct TCGCPUOps c28x_tcg_ops = {
    .initialize = c28x_tcg_init,
    .synchronize_from_tb = c28x_cpu_synchronize_from_tb,
    .cpu_exec_interrupt = c28x_cpu_exec_interrupt,
    .tlb_fill = c28x_cpu_tlb_fill,
    .do_interrupt = c28x_cpu_do_interrupt,
    .cpu_exec_halt = c28x_cpu_has_work,
};

void c28x_cpu_synchronize_from_tb(struct CPUState* cs, const TranslationBlock* tb) {
    C28XCPU* cpu = C28X_CPU(cs);
    CPUC28XState* env = &cpu->env;
    env->r[C28X_REG_PC] = tb->pc;
}

static void c28x_cpu_class_init(ObjectClass* oc, void* data) {
    printf("[C28X-CPU] c28x_cpu_class_init\n");
    C28XCPUClass* ccc = C28X_CPU_CLASS(oc);
    CPUClass* cc = CPU_CLASS(oc);
    DeviceClass* dc = DEVICE_CLASS(oc);
    ResettableClass* rc = RESETTABLE_CLASS(oc);

    device_class_set_parent_realize(dc, c28x_cpu_realizefn, &ccc->parent_realize);
    resettable_class_set_parent_phases(rc, NULL, c28x_cpu_reset, NULL, &ccc->parent_phases);

    cc->class_by_name = c28x_cpu_class_by_name;

    cc->has_work = c28x_cpu_has_work;
    cc->mmu_index = c28x_cpu_mmu_index;
    cc->dump_state = c28x_cpu_dump_state;
    cc->set_pc = c28x_cpu_set_pc;
    cc->memory_rw_debug = c28x_cpu_memory_rw_debug;
    cc->sysemu_ops = &c28x_sysemu_ops;
    cc->tcg_ops = &c28x_tcg_ops;
    cc->disas_set_info = c28x_cpu_disas_set_info;
}

#define DEFINE_C28X_CPU_TYPE(model, initfn)                                                                            \
    { .parent = TYPE_C28X_CPU, .instance_init = initfn, .name = C28X_CPU_TYPE_NAME(model), }

static const TypeInfo c28x_cpu_arch_types[] = {{
                                                   .name = TYPE_C28X_CPU,
                                                   .parent = TYPE_CPU,
                                                   .instance_size = sizeof(C28XCPU),
                                                   .instance_init = c28x_cpu_init,
                                                   .abstract = true,
                                                   .class_size = sizeof(C28XCPUClass),
                                                   .class_init = c28x_cpu_class_init,
                                               },
                                               DEFINE_C28X_CPU_TYPE("f28335", c28x_cpu_init)};

DEFINE_TYPES(c28x_cpu_arch_types)