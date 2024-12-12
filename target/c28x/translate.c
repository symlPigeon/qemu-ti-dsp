#include "qemu/osdep.h"

#include "address-mode.h"
#include "cpu.h"
#include "exec/address-spaces.h"
#include "exec/cpu_ldst.h"
#include "exec/helper-gen.h"
#include "exec/log.h"
#include "exec/translation-block.h"
#include "exec/translator.h"
#include "hw/core/tcg-cpu-ops.h"
#include "stdlib.h"
#include "tcg/tcg-op-common.h"
#include "tcg/tcg-op.h"
#include "tcg/tcg-temp-internal.h"
#include "tcg/tcg.h"

// CPU registers
static TCGv cpu_r[C28X_REG_PAGE_SIZE];

// CPU Status Registers
static TCGv cpu_sr[C28X_SR_PAGE_SIZE];

#define DISAS_EXIT   DISAS_TARGET_0 /* We want return to the cpu main loop.  */
#define DISAS_LOOKUP DISAS_TARGET_1 /* We have a variable condition exit.  */
#define DISAS_CHAIN  DISAS_TARGET_2 /* We have a single condition exit.  */

typedef struct DisasContext DisasContext;

struct DisasContext {
    DisasContextBase base;
    CPUC28XState* env;
    CPUState* cs;
    uint32_t pc;
};

void c28x_tcg_init(void) {
    int i;
    // Initialize CPU registers
    for (i = 0; i < C28X_REG_PAGE_SIZE; i++) {
        cpu_r[i] = tcg_global_mem_new_i32(tcg_env, offsetof(CPUC28XState, r[i]), c28x_cpu_r_names[i]);
    }
    // Initialize CPU Status Registers
    for (i = 0; i < C28X_SR_PAGE_SIZE; i++) {
        cpu_sr[i] = tcg_global_mem_new_i32(tcg_env, offsetof(CPUC28XState, sr[i]), c28x_cpu_sr_names[i]);
    }
}

static void gen_goto_tb(DisasContext* ctx, int n, target_ulong dest) {
    if (translator_use_goto_tb(&ctx->base, dest)) {
        tcg_gen_goto_tb(n);
        tcg_gen_movi_i32(cpu_r[C28X_REG_PC], dest);
        tcg_gen_exit_tb(ctx->base.tb, n);
    } else {
        tcg_gen_movi_i32(cpu_r[C28X_REG_PC], dest);
        tcg_gen_lookup_and_goto_ptr();
    }
    ctx->base.is_jmp = DISAS_CHAIN;
}

// Some Macros for generating code
#define _IF_COND_LABEL(label)                                                                                          \
    TCGLabel* label##_label_if = gen_new_label();                                                                      \
    TCGLabel* label##_label_else = gen_new_label();                                                                    \
    TCGLabel* label##_endif = gen_new_label();

#define IF_CONDi(label, cond, val1, val2)                                                                              \
    _IF_COND_LABEL(label)                                                                                              \
    tcg_gen_brcondi_i32(cond, val1, val2, label##_label_if);                                                           \
    tcg_gen_br(label##_label_else);                                                                                    \
    gen_set_label(label##_label_if);

#define IF_COND(label, cond, val1, val2)                                                                               \
    _IF_COND_LABEL(label)                                                                                              \
    tcg_gen_brcond_i32(cond, val1, val2, label##_label_if);                                                            \
    tcg_gen_br(label##_label_else);                                                                                    \
    gen_set_label(label##_label_if);

#define ELSE(label)                                                                                                    \
    tcg_gen_br(label##_endif);                                                                                         \
    gen_set_label(label##_label_else);

#define ENDIF(label) gen_set_label(label##_endif);

// flag options
#define clear_c_flag tcg_gen_movi_i32(cpu_sr[C_FLAG], 0)

inline static void gen_set_z_flag(TCGv_i32 val) { tcg_gen_setcondi_i32(TCG_COND_EQ, cpu_sr[Z_FLAG], val, 0); }

inline static void gen_set_n_flag(TCGv_i32 val) {
    // if bit 31 of val is 1, set N flag
    TCGv_i32 tmp = tcg_temp_new_i32();
    tcg_gen_andi_i32(tmp, val, 0x80000000);
    tcg_gen_shri_i32(tmp, tmp, 31);
    tcg_gen_mov_i32(cpu_sr[N_FLAG], tmp);
    tcg_temp_free_i32(tmp);
}

// NOTE: place this before `watch_for_overflow`, as sometimes `watch_for_overflow` will saturate the value!
inline static void watch_for_carry(TCGv_i32 dst, TCGv_i32 val1) {
    tcg_gen_setcond_i32(TCG_COND_LT, cpu_sr[C_FLAG], dst, val1);
}

#define OP_ADD_I32 0
#define OP_SUB_I32 1
inline static void watch_for_overflow(TCGv_i32 ret, TCGv_i32 val1, TCGv_i32 val2, int32_t add) {
    // A = sgn(val1), B = sgn(val2), C = sgn(ret), D = add
    // + : 0, - : 1, add : 0, sub : 1
    // underflow = (A & B & ~C & ~D) | (A & ~B & ~C & D)
    // overflow = (~A & ~B & ~C & ~D) | (~A & B & C & D)
    // reduce to:
    // underflow = (A & ~C) & (B ^ D)
    // overflow = (~A & C) & ~(B ^ D)
    TCGv_i32 sgn1 = tcg_temp_new_i32();       // sign of val1
    TCGv_i32 sgn2 = tcg_temp_new_i32();       // sign of val2
    TCGv_i32 sgn_ret = tcg_temp_new_i32();    // sign of ret
    TCGv_i32 sgn_add = tcg_temp_new_i32();    // add or sub

    tcg_gen_shri_i32(sgn1, val1, 31);
    tcg_gen_shri_i32(sgn2, val2, 31);
    tcg_gen_shri_i32(sgn_ret, ret, 31);

    tcg_gen_movi_i32(sgn_add, add);

    TCGv_i32 b_xor_d = tcg_temp_new_i32();
    TCGv_i32 b_xnor_d = tcg_temp_new_i32();
    TCGv_i32 not_a = tcg_temp_new_i32();
    TCGv_i32 not_c = tcg_temp_new_i32();

    TCGv_i32 overflow = tcg_temp_new_i32();
    TCGv_i32 underflow = tcg_temp_new_i32();
    tcg_gen_xor_i32(b_xor_d, sgn2, sgn_add);
    tcg_gen_not_i32(b_xnor_d, b_xor_d);
    tcg_gen_xori_i32(not_a, sgn1, 1);
    tcg_gen_xori_i32(not_c, sgn_ret, 1);
    tcg_gen_and_i32(underflow, sgn1, not_c);
    tcg_gen_and_i32(underflow, underflow, b_xor_d);
    tcg_gen_and_i32(overflow, not_a, sgn_ret);
    tcg_gen_and_i32(overflow, overflow, b_xnor_d);

    // clear V flag
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 0);

    IF_CONDi(ovm_set, TCG_COND_EQ, cpu_sr[OVM_FLAG], 1)

    // if OVM = 1, then OVC counter is not affected by this operation
    // but target value will saturate to 0x7FFFFFFF or 0x80000000 when overflow
    IF_CONDi(ovm_set_and_overflow, TCG_COND_NE, overflow, 0)
    // overflow
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    tcg_gen_movi_i32(cpu_r[C28X_REG_ACC], 0x7FFFFFFF);
    ELSE(ovm_set_and_overflow)
    // no overflow, just ignore this
    ENDIF(ovm_set_and_overflow)

    IF_CONDi(ovm_set_and_underflow, TCG_COND_NE, underflow, 0)
    // underflow
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    tcg_gen_movi_i32(cpu_r[C28X_REG_ACC], 0x80000000);
    ELSE(ovm_set_and_underflow)
    // no underflow, just ignore this
    ENDIF(ovm_set_and_underflow)

    ELSE(ovm_set)

    // if OVM = 0, if operation generates a positive overflow, then OVC counter is incremented
    IF_CONDi(ovm_not_set_and_overflow, TCG_COND_NE, overflow, 0)
    // overflow
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    tcg_gen_addi_i32(cpu_sr[OVC_FLAG], cpu_sr[OVC_FLAG], 1);
    ELSE(ovm_not_set_and_overflow)
    // no overflow, just ignore this
    ENDIF(ovm_not_set_and_overflow)

    // if OVM = 0, if operation generates a negative overflow, then OVC counter is decremented
    IF_CONDi(ovm_not_set_and_underflow, TCG_COND_NE, underflow, 0)
    // underflow
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    tcg_gen_subi_i32(cpu_sr[OVC_FLAG], cpu_sr[OVC_FLAG], 1);
    ELSE(ovm_not_set_and_underflow)
    // no underflow, just ignore this
    ENDIF(ovm_not_set_and_underflow)

    ENDIF(ovm_set)

    tcg_temp_free_i32(sgn1);
    tcg_temp_free_i32(sgn2);
    tcg_temp_free_i32(sgn_ret);
    tcg_temp_free_i32(sgn_add);
    tcg_temp_free_i32(b_xor_d);
    tcg_temp_free_i32(b_xnor_d);
    tcg_temp_free_i32(not_a);
    tcg_temp_free_i32(not_c);
}

// C28x address mode
#define C28X_READ_LOC16(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_16)
#define C28X_READ_LOC32(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_32)
#define C28X_WRITE_LOC16(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_16)
#define C28X_WRITE_LOC32(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_32)

//

#include "decode-insn16.c.inc"

// ==============================================
// ============== TRANSLATION CODE ==============
// ==============    16 bit insn   ==============
// ==============================================

// ** insert code here **

static bool trans_ABS_acc(DisasContext* ctx, arg_ABS_acc* a) {
    TCGLabel* label_end_acc = gen_new_label();

    // if ACC == 0x80000000
    TCGLabel* label_if_acc_neq = gen_new_label();
    tcg_gen_brcondi_i32(TCG_COND_NE, cpu_r[C28X_REG_ACC], 0x80000000, label_if_acc_neq);
    //   V = 1
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    //   if ovm = 1
    TCGLabel* label_ovm_not_1 = gen_new_label();
    tcg_gen_brcondi_i32(TCG_COND_NE, cpu_sr[OVM_FLAG], 1, label_ovm_not_1);
    //      acc = 0x7FFFFFFF
    tcg_gen_movi_i32(cpu_r[C28X_REG_ACC], 0x7FFFFFFF);
    tcg_gen_br(label_end_acc);
    //   else
    gen_set_label(label_ovm_not_1);
    //      acc = 0x80000000
    tcg_gen_movi_i32(cpu_r[C28X_REG_ACC], 0x80000000);
    tcg_gen_br(label_end_acc);

    // else
    gen_set_label(label_if_acc_neq);
    //     acc = abs(acc)
    tcg_gen_abs_i32(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC]);

    // end function
    gen_set_label(label_end_acc);

    //  N flag is set if bit 31 of acc is 1.
    TCGv_i32 tmp = tcg_temp_new_i32();
    tcg_gen_andi_i32(tmp, cpu_r[C28X_REG_ACC], 0x80000000);
    tcg_gen_shri_i32(tmp, tmp, 31);
    tcg_gen_mov_i32(cpu_sr[N_FLAG], tmp);
    // Z flag is set if acc is 0.
    TCGLabel* label_z_flag_not_set = gen_new_label();
    tcg_gen_brcondi_i32(TCG_COND_NE, cpu_r[C28X_REG_ACC], 0, label_z_flag_not_set);
    tcg_gen_movi_i32(cpu_sr[Z_FLAG], 1);
    gen_set_label(label_z_flag_not_set);
    // C is cleared
    clear_c_flag;

    tcg_temp_free_i32(tmp);
    return true;
}

static bool trans_ABSTC_acc(DisasContext* ctx, arg_ABSTC_acc* a) {
    // if acc < 0, then xor tc with 1
    TCGLabel* label_acc_not_neg = gen_new_label();
    tcg_gen_brcondi_i32(TCG_COND_GE, cpu_r[C28X_REG_ACC], 0, label_acc_not_neg);
    tcg_gen_xori_i32(cpu_sr[TC_FLAG], cpu_sr[TC_FLAG], 1);

    // behavior like ABS
    gen_set_label(label_acc_not_neg);
    trans_ABS_acc(ctx, (arg_ABS_acc*)a);
    return true;
}

static bool trans_ADDB_xarn_7bit(DisasContext* ctx, arg_ADDB_xarn_7bit* a) {
    // No flags and modes
    tcg_gen_addi_tl(cpu_r[a->xarn + C28X_REG_XAR0], cpu_r[a->xarn + C28X_REG_XAR0], a->imm7);

    return true;
}

static bool trans_LB_xar7(DisasContext* ctx, arg_LB_xar7* a) {
    // No flags and modes
    TCGv baddr = tcg_temp_new_i32();
    tcg_gen_andi_tl(baddr, cpu_r[C28X_REG_XAR7], 0x3FFFFF);

    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    ctx->base.is_jmp = DISAS_LOOKUP;

    tcg_temp_free_i32(baddr);
    return true;
}

// ==============================================
// ============== TRANSLATION END ===============
// ==============    16 bit insn  ===============
// ==============================================

#include "decode-insn32.c.inc"

// ==============================================
// ============== TRANSLATION CODE ==============
// ==============    32 bit insn   ==============
// ==============================================

// ** insert code here **
static bool trans_ADD_acc_imm16_shft(DisasContext* ctx, arg_ADD_acc_imm16_shft* a) {
    TCGv_i32 tmp = tcg_temp_new_i32();
    TCGv_i32 tmp_acc = tcg_temp_new_i32();
    // if SXM = 1
    IF_CONDi(sxm_set, TCG_COND_NE, cpu_sr[SXM_FLAG], 1)

    //   ACC = ACC + S : 16bit << shift value
    tcg_gen_movi_i32(tmp, a->imm16);
    tcg_gen_ext16s_i32(tmp, tmp);
    tcg_gen_shli_i32(tmp, tmp, a->shft);

    ELSE(sxm_set)
    //   ACC = ACC + 0 : 16bit << shift value
    tcg_gen_movi_i32(tmp, a->imm16);
    tcg_gen_shli_i32(tmp, tmp, a->shft);

    ENDIF(sxm_set)

    tcg_gen_mov_i32(tmp_acc, cpu_r[C28X_REG_ACC]);

    tcg_gen_add_i32(cpu_r[C28X_REG_ACC], tmp_acc, tmp);
    watch_for_carry(cpu_r[C28X_REG_ACC], tmp);
    watch_for_overflow(cpu_r[C28X_REG_ACC], tmp_acc, tmp, OP_ADD_I32);

    tcg_temp_free_i32(tmp);
    tcg_temp_free_i32(tmp_acc);

    gen_set_z_flag(cpu_r[C28X_REG_ACC]);
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);
    return true;
}

static bool trans_MOVL_xar0_imm22(DisasContext* ctx, arg_MOVL_xar0_imm22* a) {
    // No flags and modes
    tcg_gen_movi_tl(cpu_r[C28X_REG_XAR0], a->imm22);

    return true;
}

static bool trans_ADD_acc_loc16_t(DisasContext* ctx, arg_ADD_acc_loc16_t* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv t = tcg_temp_new_i32();
    tcg_gen_shri_tl(t, cpu_r[C28X_REG_XT], 16);

    IF_CONDi(use_sxm, TCG_COND_EQ, cpu_sr[SXM_FLAG], 1)
    tcg_gen_ext32s_tl(target_value, target_value);
    ELSE(use_sxm)
    // no need to sign extend
    ENDIF(use_sxm)

    tcg_gen_shl_tl(target_value, target_value, t);

    TCGv temp_acc = tcg_temp_new_i32();
    tcg_gen_mov_i32(temp_acc, cpu_r[C28X_REG_ACC]);
    tcg_gen_add_tl(cpu_r[C28X_REG_ACC], temp_acc, target_value);

    watch_for_carry(cpu_r[C28X_REG_ACC], temp_acc);
    watch_for_overflow(cpu_r[C28X_REG_ACC], temp_acc, target_value, OP_ADD_I32);

    gen_set_z_flag(cpu_r[C28X_REG_ACC]);
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);

    tcg_temp_free_i32(temp_acc);
    tcg_temp_free_i32(target_value);
    tcg_temp_free_i32(t);
    return true;
}

static bool trans_MOV_acc_loc16_t(DisasContext* ctx, arg_MOV_acc_loc16_t* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);

    IF_CONDi(use_sxm, TCG_COND_EQ, cpu_sr[SXM_FLAG], 1)
    tcg_gen_ext32s_tl(target_value, target_value);
    ELSE(use_sxm)
    // no need to sign extend
    ENDIF(use_sxm)

    tcg_gen_mov_i32(cpu_r[C28X_REG_ACC], target_value);

    gen_set_z_flag(cpu_r[C28X_REG_ACC]);
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);

    tcg_temp_free_i32(target_value);
    return true;
}

// ==============================================
// ============== TRANSLATION END ===============
// ==============    32 bit insn  ===============
// ==============================================

static void c28x_tr_init_disas_context(DisasContextBase* dcbase, CPUState* cs) {
    printf("[C28X-TCG] c28x_tr_init_disas_context\n");
    CPUC28XState* env = cpu_env(cs);
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    ctx->env = env;
    ctx->pc = ctx->base.pc_first;
    // log out ctx base params
    printf("[C28X-TCG] ctx->base->num_insns: %d\n", ctx->base.num_insns);
}

static void c28x_tr_tb_start(DisasContextBase* dcbase, CPUState* cs) {}

static void c28x_tr_tb_stop(DisasContextBase* dcbase, CPUState* cs) {
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    switch (ctx->base.is_jmp) {
    case DISAS_NEXT:
    case DISAS_TOO_MANY:
    case DISAS_CHAIN:
        gen_goto_tb(ctx, 1, ctx->base.pc_next);
        tcg_gen_movi_tl(cpu_r[C28X_REG_PC], ctx->base.pc_next);
        /* fall through */
    case DISAS_LOOKUP:
    case DISAS_EXIT:
        tcg_gen_exit_tb(NULL, 0);
        break;
    case DISAS_NORETURN:
        break;
    default:
        printf("[C28X-TCG] c28x_tr_tb_stop: unknown jump type\n");
        g_assert_not_reached();
    }
}

static void c28x_insn_start(DisasContextBase* dcbase, CPUState* cs) {
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    tcg_gen_insn_start(ctx->base.pc_next);
}

static void c28x_tr_translate_insn(DisasContextBase* dcbase, CPUState* cs) {
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    uint16_t opcode16;

    // load first 16-bits for decoding
    opcode16 = cpu_lduw_be_data(ctx->env, ctx->base.pc_next);

    if (!decode_insn16(ctx, opcode16)) {
        // load next 16-bits for decoding
        uint32_t opcode32 = cpu_lduw_be_data(ctx->env, ctx->base.pc_next + 2) | (opcode16 << 16);
        if (!decode_insn32(ctx, opcode32)) {
            error_report("[C28X-TCG] c28x_tr_translate_insn: unknown instruction, pc: 0x%lx", ctx->base.pc_next);
            error_report("[C28X-TCG] c28x_tr_translate_insn: opcode16: 0x%x, opcode32: 0x%x", opcode16, opcode32);
            gen_helper_raise_illegal_instruction(tcg_env);

            ctx->base.is_jmp = DISAS_NORETURN;
            return;
        } else {
            // legal 32-bit instruction
            ctx->base.pc_next += 4;
        }
    } else {
        // legal 16-bit instruction
        ctx->base.pc_next += 2;
    }
}

static bool c28x_tr_disas_log(const DisasContextBase* dcbase, CPUState* cs, FILE* log_file) {
    fprintf(log_file, "[C28X-TCG] pc: 0x%lx\n", dcbase->pc_first);
    fprintf(log_file, "IN: %s\n", lookup_symbol(dcbase->pc_first));
    target_disas(log_file, cs, dcbase);
    return true;
}

static const TranslatorOps c28x_tr_ops = {
    .init_disas_context = c28x_tr_init_disas_context,
    .tb_start = c28x_tr_tb_start,
    .insn_start = c28x_insn_start,
    .translate_insn = c28x_tr_translate_insn,
    .tb_stop = c28x_tr_tb_stop,
    .disas_log = c28x_tr_disas_log,
};

void gen_intermediate_code(CPUState* cs, TranslationBlock* tb, int* max_insns, vaddr pc, void* host_pc) {
    DisasContext dc = {};
    translator_loop(cs, tb, max_insns, pc, host_pc, &c28x_tr_ops, &dc.base);
}