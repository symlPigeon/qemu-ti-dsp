#include "address-mode.h"
#include "condition.h"
#include "cpu.h"
#include "disas/disas.h"
#include "exec/cpu_ldst.h"
#include "exec/helper-gen.h"
#include "exec/helper-proto.h"
#include "exec/translator.h"
#include "mode-flags.h"
#include "tcg/tcg-cond.h"
#include "tcg/tcg-op-common.h"
#include "tcg/tcg-op.h"
#include "tcg/tcg.h"

#define HELPER_H "helper.h"
#include "exec/helper-info.c.inc"
#undef HELPER_H

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
    target_long pc;
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
    ctx->base.is_jmp = DISAS_NORETURN;
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
#define SKIP()       ;

// flag options
#define clear_c_flag tcg_gen_movi_i32(cpu_sr[C_FLAG], 0)

inline static void gen_set_z_flag(TCGv_i32 val) { tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], val, 0); }

inline static void gen_set_n_flag(TCGv_i32 val) { tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], val, 0); }

// NOTE: place this before `watch_for_overflow`, as sometimes `watch_for_overflow` will saturate the value!
inline static void watch_for_carry(TCGv_i32 dst, TCGv_i32 val1) {
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[C_FLAG], dst, val1);
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
    tcg_gen_movi_i32(ret, 0x7FFFFFFF);
    ELSE(ovm_set_and_overflow)
    // no overflow, just ignore this
    ENDIF(ovm_set_and_overflow)

    IF_CONDi(ovm_set_and_underflow, TCG_COND_NE, underflow, 0)
    // underflow
    tcg_gen_movi_i32(cpu_sr[V_FLAG], 1);
    tcg_gen_movi_i32(ret, 0x80000000);
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
}

// C28x address mode
#define C28X_READ_LOC16(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_16, 0)
#define C28X_READ_LOC32(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_32, 0)
#define C28X_WRITE_LOC16(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_16, 0)
#define C28X_WRITE_LOC32(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_32, 0)

// C28x Read and Write address mode
#define C28X_READ_LOC16_RMW(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_16, 1)
#define C28X_READ_LOC32_RMW(loc, reg)  C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_READ, C28X_LOC_32, 1)
#define C28X_WRITE_LOC16_RMW(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_16, 1)
#define C28X_WRITE_LOC32_RMW(loc, reg) C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, C28X_MEM_ACCESS_WRITE, C28X_LOC_32, 1)

// Sign extend value
#define SXM_EXTEND(val)                                                                                                \
    IF_CONDi(sxm_set, TCG_COND_NE, cpu_sr[SXM_FLAG], 1)                                                                \
    tcg_gen_ext32s_tl(val, val);                                                                                       \
    ELSE(sxm_set)                                                                                                      \
    ENDIF(sxm_set)

// ADD to ACC with value and shift
#define _INTERNAL_ADD_TO_ACC_WITH_FLAGS(value, shift)                                                                  \
    tcg_gen_shl_tl(value, value, shift);                                                                               \
    TCGv _macro_internal_temp_acc = tcg_temp_new_i32();                                                                \
    tcg_gen_mov_tl(_macro_internal_temp_acc, cpu_r[C28X_REG_ACC]);                                                     \
    tcg_gen_add_tl(cpu_r[C28X_REG_ACC], _macro_internal_temp_acc, value);                                              \
    watch_for_carry(cpu_r[C28X_REG_ACC], _macro_internal_temp_acc);                                                    \
    watch_for_overflow(cpu_r[C28X_REG_ACC], _macro_internal_temp_acc, value, OP_ADD_I32);                              \
    gen_set_z_flag(cpu_r[C28X_REG_ACC]);                                                                               \
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);

#define ADD_TO_ACC_WITH_FLAGS(value, shift)                                                                            \
    TCGv _macro_arg_value = tcg_temp_new_i32();                                                                        \
    tcg_gen_mov_tl(_macro_arg_value, value);                                                                           \
    SXM_EXTEND(_macro_arg_value);                                                                                      \
    _INTERNAL_ADD_TO_ACC_WITH_FLAGS(_macro_arg_value, shift);

#define ADD_TO_ACC_WITH_FLAGS_NO_SXM(value, shift)                                                                     \
    TCGv _macro_arg_value = tcg_temp_new_i32();                                                                        \
    tcg_gen_mov_tl(_macro_arg_value, value);                                                                           \
    _INTERNAL_ADD_TO_ACC_WITH_FLAGS(_macro_arg_value, shift);

inline static void gen_flag_add_loc16(TCGv s, TCGv a, TCGv b) {
    TCGv sum = tcg_temp_new_i32();
    tcg_gen_mov_tl(sum, s);
    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    tcg_gen_mov_tl(adder_1, a);
    tcg_gen_mov_tl(adder_2, b);

    // set Z flag when sum is zero (Z flag)
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], sum, 0);
    // fetch the sign bit of sum
    TCGv neg_flag = tcg_temp_new_i32();
    tcg_gen_shri_tl(neg_flag, sum, 15);
    tcg_gen_andi_tl(cpu_sr[N_FLAG], neg_flag, 1);

    // set C flag, that is 16th bit, higher bit should be 0
    tcg_gen_shri_tl(cpu_sr[C_FLAG], sum, 16);

    // check overflow, first, adder_1 and adder_2 share the same sign (XNOR)
    tcg_gen_shri_tl(adder_1, adder_1, 15);
    tcg_gen_shri_tl(adder_2, adder_2, 15);
    TCGv overflow_1 = tcg_temp_new_i32();
    tcg_gen_xor_tl(overflow_1, adder_1, adder_2);
    tcg_gen_not_tl(overflow_1, overflow_1);
    // next, sum and adder_1 sign is different (XOR)
    tcg_gen_shri_tl(sum, sum, 15);
    TCGv overflow_2 = tcg_temp_new_i32();
    tcg_gen_xor_tl(overflow_2, sum, adder_1);
    // if both conditions are met, then overflow (V Flag)
    tcg_gen_and_tl(cpu_sr[V_FLAG], overflow_1, overflow_2);
}

inline static void gen_and_dst(TCGv dst, TCGv mask, bool check_flag) {
    tcg_gen_and_tl(dst, dst, mask);
    if (check_flag) {
        gen_set_z_flag(dst);
        gen_set_n_flag(dst);
    }
}

#define REG_T(name, lsb)                                                                                               \
    TCGv name = tcg_temp_new_i32();                                                                                    \
    tcg_gen_shri_tl(name, cpu_r[C28X_REG_XT], 16);                                                                     \
    tcg_gen_andi_tl(name, name, (1 << lsb) - 1);

#define REG_AX_R(name, AX)                                                                                             \
    TCGv name = tcg_temp_new_i32();                                                                                    \
    if (AX)                                                                                                            \
        tcg_gen_shri_tl(name, cpu_r[C28X_REG_ACC], 16);                                                                \
    else                                                                                                               \
        tcg_gen_andi_tl(name, cpu_r[C28X_REG_ACC], 0xffff);

#define REG_AX_W(value, AX)                                                                                            \
    if (AX) {                                                                                                          \
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0x0000ffff);                                         \
        tcg_gen_shli_tl(value, value, 16);                                                                             \
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], value);                                                \
    } else {                                                                                                           \
        tcg_gen_andi_tl(value, value, 0xffff);                                                                         \
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0xffff0000);                                         \
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], value);                                                \
    }

#define LSL_TARGET_SHFT(dst, shft)                                                                                     \
    tcg_gen_shl_tl(dst, dst, shft);                                                                                    \
    tcg_gen_shri_tl(cpu_sr[C_FLAG], dst, 31);                                                                          \
    tcg_gen_shli_tl(dst, dst, 1);

#define LSL_TARGET_FLAG_TEST(dst)                                                                                      \
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], dst, 0);                                                          \
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], dst, 0);

#define CHECK_ACC_P_NZ                                                                                                 \
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], cpu_r[C28X_REG_ACC], 0);                                          \
    TCGv acc_zero = tcg_temp_new_i32();                                                                                \
    TCGv p_zero = tcg_temp_new_i32();                                                                                  \
    tcg_gen_setcondi_tl(TCG_COND_EQ, acc_zero, cpu_r[C28X_REG_ACC], 0);                                                \
    tcg_gen_setcondi_tl(TCG_COND_EQ, p_zero, cpu_r[C28X_REG_P], 0);                                                    \
    tcg_gen_and_tl(cpu_sr[Z_FLAG], acc_zero, p_zero);

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

static bool trans_ADD_acc_loc16(DisasContext* ctx, arg_ADD_acc_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv shft = tcg_constant_i32(0);

    ADD_TO_ACC_WITH_FLAGS(target_value, shft)

    return true;
}

static bool trans_ADD_acc_loc16_shl16(DisasContext* ctx, arg_ADD_acc_loc16_shl16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv shft = tcg_constant_i32(16);

    ADD_TO_ACC_WITH_FLAGS(target_value, shft)

    return true;
}

static bool trans_ADD_ax_loc16(DisasContext* ctx, arg_ADD_ax_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);

    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    TCGv add_sum = tcg_temp_new_i32();
    tcg_gen_mov_tl(adder_1, target_value);

    if (a->ax == 1) {
        // AH
        tcg_gen_shri_tl(adder_2, cpu_r[C28X_REG_ACC], 16);
        tcg_gen_shli_tl(target_value, target_value, 16);
        tcg_gen_add_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], target_value);
    } else {
        // AL
        tcg_gen_andi_tl(adder_2, cpu_r[C28X_REG_ACC], 0xffff);
        // Not sure if this add will affect AH
        // assume not
        TCGv temp = tcg_temp_new_i32();
        tcg_gen_add_tl(temp, cpu_r[C28X_REG_ACC], target_value);
        tcg_gen_andi_tl(temp, temp, 0x0000ffff);
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0xffff0000);
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], temp);
    }

    // calculate the actual sum of AX
    tcg_gen_add_tl(add_sum, adder_1, adder_2);

    gen_flag_add_loc16(add_sum, adder_1, adder_2);

    return true;
}

static bool trans_ADD_loc16_ax(DisasContext* ctx, arg_ADD_loc16_ax* a) {
    // so this should be a read-modify-write operation
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);

    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    TCGv add_sum = tcg_temp_new_i32();

    tcg_gen_mov_tl(adder_1, target_value);
    if (a->ax == 1) {
        // AH
        tcg_gen_shri_tl(adder_2, cpu_r[C28X_REG_ACC], 16);
    } else {
        // AL
        tcg_gen_andi_tl(adder_2, cpu_r[C28X_REG_ACC], 0xffff);
    }
    tcg_gen_add_tl(add_sum, adder_1, adder_2);
    TCGv add_sum_16 = tcg_temp_new_i32();
    tcg_gen_andi_tl(add_sum_16, add_sum, 0xffff);
    C28X_WRITE_LOC16_RMW(a->loc16, add_sum_16);

    gen_flag_add_loc16(add_sum, adder_1, adder_2);

    return true;
}

static bool trans_ADD_acc_imm8(DisasContext* ctx, arg_ADD_acc_imm8* a) {
    TCGv imm8 = tcg_constant_tl(a->imm8);
    TCGv shft = tcg_constant_tl(0);
    ADD_TO_ACC_WITH_FLAGS_NO_SXM(imm8, shft)

    return true;
}

static bool trans_ADDB_ax_imm8s(DisasContext* ctx, arg_ADDB_ax_imm8s* a) {
    // NOTE: not sure if this is correct
    TCGv imm8s = tcg_constant_tl(a->imm8s);
    tcg_gen_ext8s_tl(imm8s, imm8s);
    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    TCGv add_sum = tcg_temp_new_i32();

    tcg_gen_mov_tl(adder_1, imm8s);
    if (a->ax == 1) {
        // AH
        tcg_gen_shri_tl(adder_2, cpu_r[C28X_REG_ACC], 16);
        tcg_gen_shli_tl(imm8s, imm8s, 16);
        tcg_gen_add_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], imm8s);
    } else {
        // AL
        tcg_gen_andi_tl(adder_2, cpu_r[C28X_REG_ACC], 0xffff);
        // Not sure if this add will affect AH
        // assume not
        TCGv temp = tcg_temp_new_i32();
        tcg_gen_add_tl(temp, cpu_r[C28X_REG_ACC], imm8s);
        tcg_gen_andi_tl(temp, temp, 0x0000ffff);
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0xffff0000);
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], temp);
    }

    tcg_gen_add_tl(add_sum, adder_1, adder_2);

    gen_flag_add_loc16(add_sum, adder_1, adder_2);

    return true;
}

static bool trans_ADDB_sp_imm7(DisasContext* ctx, arg_ADDB_sp_imm7* a) {
    // No flags and modes
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], a->imm7);

    return true;
}

static bool trans_ADDB_xarn_7bit(DisasContext* ctx, arg_ADDB_xarn_7bit* a) {
    // No flags and modes
    tcg_gen_addi_tl(cpu_r[a->xarn + C28X_REG_XAR0], cpu_r[a->xarn + C28X_REG_XAR0], a->imm7);

    return true;
}

static bool trans_ADDCU_acc_loc16(DisasContext* ctx, arg_ADDCU_acc_loc16* a) {
    // ACC = ACC + 0:[loc16] + Carry
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv shft = tcg_constant_i32(0);

    tcg_gen_ext16u_tl(target_value, target_value);    // zero extend first
    tcg_gen_add_tl(target_value, target_value, cpu_sr[C_FLAG]);

    ADD_TO_ACC_WITH_FLAGS_NO_SXM(target_value, shft);

    return true;
}

static bool trans_ADDL_acc_loc32(DisasContext* ctx, arg_ADDL_acc_loc32* a) {
    // ACC = ACC + [loc32]
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC32(a->loc32, target_value);
    TCGv shft = tcg_constant_i32(0);

    ADD_TO_ACC_WITH_FLAGS_NO_SXM(target_value, shft);

    return true;
}

static bool trans_ADDU_acc_loc16(DisasContext* ctx, arg_ADDU_acc_loc16* a) {
    // ACC = ACC + 0:[loc16]
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv shft = tcg_constant_i32(0);

    ADD_TO_ACC_WITH_FLAGS_NO_SXM(target_value, shft);

    return true;
}

static bool trans_ADRK_imm8(DisasContext* ctx, arg_ADRK_imm8* a) {
    // add to XAR(ARP), no other flags
    TCGLabel* xar_label[9];
    for (int i = 0; i < 9; i++) {
        xar_label[i] = gen_new_label();
    }
    for (int i = 0; i < 8; i++) {
        gen_set_label(xar_label[i]);
        tcg_gen_brcondi_tl(TCG_COND_NE, cpu_sr[ARP_FLAG], i, xar_label[i + 1]);
        tcg_gen_addi_tl(cpu_r[C28X_REG_XAR0 + i], cpu_r[C28X_REG_XAR0 + i], a->imm8);
        tcg_gen_br(xar_label[8]);
    }
    gen_set_label(xar_label[8]);
    return true;
}

static bool trans_AND_acc_loc16(DisasContext* ctx, arg_AND_acc_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);

    gen_and_dst(cpu_r[C28X_REG_ACC], target_value, true);

    return true;
}

static bool trans_AND_loc16_ax(DisasContext* ctx, arg_AND_loc16_ax* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);
    REG_AX_R(ax, a->ax);
    TCGv result = tcg_temp_new_i32();
    tcg_gen_and_tl(result, target_value, ax);
    C28X_WRITE_LOC16_RMW(a->loc16, result);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], result, 15);

    return true;
}

static bool trans_AND_ax_loc16(DisasContext* ctx, arg_AND_ax_loc16* a) {
    // AX = [loc16] AND 16bit
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);

    TCGv result = tcg_temp_new_i32();
    if (a->ax == 1) {
        // AH
        tcg_gen_shli_tl(target_value, target_value, 16);
        tcg_gen_and_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], target_value);
        tcg_gen_shri_tl(result, cpu_r[C28X_REG_ACC], 16);
    } else {
        // AL
        tcg_gen_and_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], target_value);
        tcg_gen_andi_tl(result, cpu_r[C28X_REG_ACC], 0xffff);
    }
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], result, 15);

    return true;
}

static bool trans_AND_ax_imm8s(DisasContext* ctx, arg_AND_ax_imm8s* a) {
    // AX = AX AND 0:8bit, to reuse code, we call it imm8s, but it should be unsigned
    TCGv mask = tcg_constant_tl(a->imm8s);
    tcg_gen_ori_tl(mask, mask, 0xffff0000);    // 8 bit mask

    TCGv result = tcg_temp_new_i32();
    if (a->ax == 1) {
        // AH
        tcg_gen_shli_tl(mask, mask, 16);
        tcg_gen_ori_tl(mask, mask, 0x0000ffff);
        tcg_gen_and_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], mask);
        tcg_gen_shri_tl(result, cpu_r[C28X_REG_ACC], 16);
    } else {
        // AL
        tcg_gen_and_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], mask);
        tcg_gen_andi_tl(result, cpu_r[C28X_REG_ACC], 0xffff);
    }

    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], result, 15);

    return true;
}

static bool trans_ASP(DisasContext* ctx, arg_ASP* a) {
    // if SP = odd
    //  SP = SP + 1
    //  SPA = 1
    // else
    //  SPA = 0
    TCGv sp_odd = tcg_temp_new_i32();
    tcg_gen_andi_tl(sp_odd, cpu_r[C28X_REG_SP], 1);

    IF_CONDi(sp_odd_set, TCG_COND_NE, sp_odd, 0)
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    tcg_gen_movi_i32(cpu_sr[SPA_FLAG], 1);
    ELSE(sp_odd_set)
    tcg_gen_movi_i32(cpu_sr[SPA_FLAG], 0);
    ENDIF(sp_odd_set)

    return true;
}

static bool trans_ASR_ax_shft(DisasContext* ctx, arg_ASR_ax_shft* a) {
    // shift value is a->shft + 1
    // for example, ffa0 => ASR AL, 1
    // we should take last out bit as C_FLAG
    REG_AX_R(value, a->ax);
    // sign extend
    tcg_gen_ext16s_tl(value, value);
    // Now LSB of value is the C_FLAG, which is the last bit out
    tcg_gen_shri_tl(value, value, a->shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], value, 1);
    // Now value is the result
    tcg_gen_shri_tl(value, value, 1);
    tcg_gen_andi_tl(value, value, 0xffff);
    // generate N and Z flags
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], value, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], value, 15);

    // write back to AH / AL
    REG_AX_W(value, a->ax);

    return true;
}

static bool trans_ASR_ax_t(DisasContext* ctx, arg_ASR_ax_t* a) {
    TCGLabel* label_end = gen_new_label();
    REG_T(t, 4);    // 0..15
    // if t == 0 then clear this flag, else C_FLAG will be set later
    tcg_gen_mov_tl(cpu_sr[C_FLAG], t);
    // t == 0 do nothing
    tcg_gen_brcondi_tl(TCG_COND_EQ, t, 0, label_end);
    tcg_gen_subi_tl(t, t, 1);    // fuck me

    REG_AX_R(value, a->ax);

    tcg_gen_ext16s_tl(value, value);
    tcg_gen_shr_tl(value, value, t);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], value, 1);
    tcg_gen_shri_tl(value, value, 1);
    tcg_gen_andi_tl(value, value, 0xffff);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], value, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], value, 15);

    REG_AX_W(value, a->ax);

    gen_set_label(label_end);

    return true;
}

static bool trans_ASR64_acc_p_shft(DisasContext* ctx, arg_ASR64_acc_p_shft* a) {
    // move shft + 1
    TCGv shft_value = tcg_temp_new_i32();

    TCGv last_out_bit = tcg_temp_new_i32();
    tcg_gen_shri_tl(last_out_bit, cpu_r[C28X_REG_P], a->shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], last_out_bit, 1);

    tcg_gen_andi_tl(shft_value, cpu_r[C28X_REG_ACC], 1U << a->shft);
    tcg_gen_shri_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], a->shft + 1);
    tcg_gen_sari_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], a->shft + 1);

    tcg_gen_shli_tl(shft_value, shft_value, 31 - a->shft);
    tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft_value);

    CHECK_ACC_P_NZ

    return true;
}

static bool trans_ASR64_acc_p_t(DisasContext* ctx, arg_ASR64_acc_p_t* a) {
    TCGLabel* label_end = gen_new_label();

    REG_T(shft, 6);
    TCGv shft_value = tcg_temp_new_i32();
    TCGv last_out_bit = tcg_temp_new_i32();
    TCGv mask = tcg_constant_tl(1);
    TCGv shft_p = tcg_temp_new_i32();
    TCGv lshft = tcg_temp_new_i32();
    TCGv width = tcg_constant_tl(31);

    tcg_gen_mov_tl(cpu_sr[C_FLAG], shft);
    tcg_gen_brcondi_tl(TCG_COND_EQ, shft, 0, label_end);
    tcg_gen_subi_tl(shft, shft, 1);

    tcg_gen_shr_tl(last_out_bit, cpu_r[C28X_REG_P], shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], last_out_bit, 1);

    tcg_gen_shl_tl(mask, mask, shft);
    tcg_gen_addi_tl(shft_p, shft, 1);

    tcg_gen_and_tl(shft_value, cpu_r[C28X_REG_ACC], mask);
    tcg_gen_shr_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], shft_p);
    tcg_gen_sar_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft_p);

    tcg_gen_sub_tl(lshft, width, shft);

    tcg_gen_shl_tl(shft_value, shft_value, width);
    tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft_value);

    CHECK_ACC_P_NZ

    gen_set_label(label_end);

    return true;
}

static bool trans_ASRL_acc_t(DisasContext* ctx, arg_ASRL_acc_t* a) {
    TCGLabel* label_end = gen_new_label();

    REG_T(shft, 5);

    tcg_gen_mov_tl(cpu_sr[C_FLAG], shft);
    tcg_gen_brcondi_tl(TCG_COND_EQ, shft, 0, label_end);
    tcg_gen_subi_tl(shft, shft, 1);

    tcg_gen_sar_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], 1);
    tcg_gen_sari_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 1);

    tcg_gen_shri_tl(cpu_sr[N_FLAG], cpu_r[C28X_REG_ACC], 31);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], cpu_r[C28X_REG_ACC], 0);

    gen_set_label(label_end);

    return true;
}

static bool trans_C27MAP(DisasContext* ctx, arg_C27MAP* a) {
    // Clear M0M1MAP bit
    tcg_gen_movi_tl(cpu_sr[M0M1MAP_FLAG], 0);
    return true;
}

static bool trans_C27OBJ(DisasContext* ctx, arg_C27OBJ* a) {
    // Clear OBJMODE bit
    tcg_gen_movi_tl(cpu_sr[OBJMODE_FLAG], 0);
    return true;
}

static bool trans_C28ADDR(DisasContext* ctx, arg_C28ADDR* a) {
    // Clear the AMODE status bit
    tcg_gen_movi_tl(cpu_sr[AMODE_FLAG], 0);

    return true;
}

static bool trans_C28MAP(DisasContext* ctx, arg_C28MAP* a) {
    // Set M0M1MAP bit
    tcg_gen_movi_tl(cpu_sr[M0M1MAP_FLAG], 1);
    return true;
}

static bool trans_C28OBJ(DisasContext* ctx, arg_C28OBJ* a) {
    // set objmode
    tcg_gen_movi_tl(cpu_sr[OBJMODE_FLAG], 1);
    return true;
}

static bool trans_CLRC_ovc(DisasContext* ctx, arg_CLRC_ovc* a) {
    // clear OVC
    tcg_gen_movi_tl(cpu_sr[OVC_FLAG], 0);
    return true;
}

static bool trans_CLRC_xf(DisasContext* ctx, arg_CLRC_xf* a) {
    // clear XF
    tcg_gen_movi_tl(cpu_sr[XF_FLAG], 0);
    return true;
}

static bool trans_CLRC_mode(DisasContext* ctx, arg_CLRC_mode* a) {
    // clear mode
    C28X_CLRC_MODE(cpu_sr, a->mode);
    return true;
}

static bool trans_CMP_ax_loc16(DisasContext* ctx, arg_CMP_ax_loc16* a) {
    // Set flags on (AX - [loc16])
    TCGv loc_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, loc_value);
    REG_AX_R(ax_value, a->ax);
    TCGv result = tcg_temp_new_i32();
    // signed expand to 32bit
    tcg_gen_ext16s_tl(loc_value, loc_value);
    tcg_gen_ext16s_tl(ax_value, ax_value);
    tcg_gen_sub_tl(result, ax_value, loc_value);
    // set c flag when no borrow
    tcg_gen_setcond_tl(TCG_COND_GE, cpu_sr[C_FLAG], ax_value, loc_value);
    // set z flag when result is 0
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    // set n flag when result is negative
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[N_FLAG], result, 0);
    return true;
}

static bool trans_CMP64_acc_p(DisasContext* ctx, arg_CMP64_acc_p* a) {
    // set flags on ACC:P
    // when determine N flag, use V flag as well to take overflow into account
    TCGv acc_flag = tcg_temp_new_i32();
    tcg_gen_shri_tl(acc_flag, cpu_r[C28X_REG_ACC], 31);
    // set N flag
    tcg_gen_mov_tl(cpu_sr[N_FLAG], acc_flag);
    // but if v set, then N flag should be inverted(overflow)
    IF_CONDi(v_set, TCG_COND_NE, cpu_sr[V_FLAG], 0)
    tcg_gen_xori_tl(cpu_sr[N_FLAG], cpu_sr[N_FLAG], 1);
    ELSE(v_set)
    SKIP()
    ENDIF(v_set)
    // set Z flag, iff ACC:P is 0
    TCGv zero_flag = tcg_temp_new_i32();
    tcg_gen_or_tl(zero_flag, cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_P]);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], zero_flag, 0);
    // clear v flag
    tcg_gen_movi_tl(cpu_sr[V_FLAG], 0);
    return true;
}

static bool trans_CMPB_ax_imm8(DisasContext* ctx, arg_CMPB_ax_imm8* a) {
    REG_AX_R(ax_value, a->ax);
    TCGv imm8 = tcg_constant_tl(a->imm8s);
    tcg_gen_ext8u_tl(imm8, imm8);
    tcg_gen_ext16u_tl(ax_value, ax_value);
    TCGv result = tcg_temp_new_i32();
    tcg_gen_sub_tl(result, ax_value, imm8);
    tcg_gen_setcond_tl(TCG_COND_GE, cpu_sr[C_FLAG], ax_value, imm8);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[N_FLAG], result, 0);

    return true;
}

static bool trans_CMPL_acc_loc32(DisasContext* ctx, arg_CMPL_acc_loc32* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC32(a->loc32, target_value);
    TCGv result = tcg_temp_new_i32();
    tcg_gen_sub_tl(result, cpu_r[C28X_REG_ACC], target_value);
    tcg_gen_setcond_tl(TCG_COND_GE, cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], target_value);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    // NOTE: not sure if this is correct
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[N_FLAG], cpu_r[C28X_REG_ACC], target_value);
    return true;
}

static bool trans_CMPL_acc_p_pm(DisasContext* ctx, arg_CMPL_acc_p_pm* a) {
    TCGv shft_p = tcg_temp_new_i32();
    tcg_gen_shr_tl(shft_p, cpu_r[C28X_REG_P], cpu_sr[PM_FLAG]);
    TCGv result = tcg_temp_new_i32();
    tcg_gen_sub_tl(result, cpu_r[C28X_REG_ACC], shft_p);
    tcg_gen_setcond_tl(TCG_COND_GE, cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], shft_p);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[N_FLAG], cpu_r[C28X_REG_ACC], shft_p);
    return true;
}

static bool trans_CMPR0(DisasContext* ctx, arg_CMPR0* a) {
    // if (AR0 = AR[ARP]) then TC = 1 else TC = 0
    // get AR[ARP]
    TCGv ar_arp = tcg_temp_new_i32();
    TCGLabel* arp_labels[9];
    for (int i = 0; i < 9; i++) {
        arp_labels[i] = gen_new_label();
    }

    for (int i = 0; i < 8; i++) {
        gen_set_label(arp_labels[i]);
        tcg_gen_brcondi_tl(TCG_COND_NE, cpu_sr[ARP_FLAG], i, arp_labels[i + 1]);
        tcg_gen_mov_tl(ar_arp, cpu_r[C28X_REG_XAR0 + i]);
        tcg_gen_br(arp_labels[8]);
    }
    gen_set_label(arp_labels[8]);

    // compare with AR0
    TCGv ar0 = tcg_temp_new_i32();
    tcg_gen_mov_tl(ar0, cpu_r[C28X_REG_XAR0]);

    // only low 16 bits
    tcg_gen_andi_tl(ar_arp, ar_arp, 0xffff);
    tcg_gen_andi_tl(ar0, ar0, 0xffff);

    // compare
    tcg_gen_setcond_tl(TCG_COND_EQ, cpu_sr[TC_FLAG], ar_arp, ar0);

    return true;
}

static bool trans_CMPR3(DisasContext* ctx, arg_CMPR3* a) {
    // if (AR0 != AR[ARP]) then TC = 1 else TC = 0
    // get AR[ARP]
    TCGv ar_arp = tcg_temp_new_i32();
    TCGLabel* arp_labels[9];
    for (int i = 0; i < 9; i++) {
        arp_labels[i] = gen_new_label();
    }

    for (int i = 0; i < 8; i++) {
        gen_set_label(arp_labels[i]);
        tcg_gen_brcondi_tl(TCG_COND_NE, cpu_sr[ARP_FLAG], i, arp_labels[i + 1]);
        tcg_gen_mov_tl(ar_arp, cpu_r[C28X_REG_XAR0 + i]);
        tcg_gen_br(arp_labels[8]);
    }
    gen_set_label(arp_labels[8]);

    // compare with AR0
    TCGv ar0 = tcg_temp_new_i32();
    tcg_gen_mov_tl(ar0, cpu_r[C28X_REG_XAR0]);

    // only low 16 bits
    tcg_gen_andi_tl(ar_arp, ar_arp, 0xffff);
    tcg_gen_andi_tl(ar0, ar0, 0xffff);

    // compare
    tcg_gen_setcond_tl(TCG_COND_NE, cpu_sr[TC_FLAG], ar_arp, ar0);

    return true;
}

static bool trans_CSB_acc(DisasContext* ctx, arg_CSB_acc* a) {
    // count leading 0 or 1
    TCGv sign = tcg_temp_new_i32();
    tcg_gen_shri_tl(sign, cpu_r[C28X_REG_ACC], 31);
    TCGv acc = tcg_temp_new_i32();
    tcg_gen_mov_tl(acc, cpu_r[C28X_REG_ACC]);
    IF_CONDi(sign_set, TCG_COND_EQ, sign, 1)
    tcg_gen_not_tl(acc, acc);
    tcg_gen_movi_tl(cpu_sr[N_FLAG], 1);
    tcg_gen_movi_tl(cpu_sr[TC_FLAG], 1);
    ELSE(sign_set)
    tcg_gen_movi_tl(cpu_sr[N_FLAG], 0);
    tcg_gen_movi_tl(cpu_sr[TC_FLAG], 0);
    ENDIF(sign_set)
    TCGv count = tcg_temp_new_i32();
    tcg_gen_ctz_tl(count, acc, tcg_constant_tl(0));
    tcg_gen_subi_tl(count, count, 1);
    tcg_gen_andi_tl(cpu_r[C28X_REG_XT], cpu_r[C28X_REG_XT], 0xffff);
    tcg_gen_shli_tl(count, count, 16);
    tcg_gen_or_tl(cpu_r[C28X_REG_XT], cpu_r[C28X_REG_XT], count);

    return true;
}

static bool trans_DEC_loc16(DisasContext* ctx, arg_DEC_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);
    tcg_gen_ext16s_tl(target_value, target_value);
    tcg_gen_setcondi_tl(TCG_COND_NE, cpu_sr[C_FLAG], target_value, 0);    // borrow => clear c_flag
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[V_FLAG], target_value, 0);    // overflow iff loc16 == 1
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], target_value, 1);    // zero iff loc16 == 1
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], target_value, 1);    // negative iff loc16 < 1
    tcg_gen_subi_tl(target_value, target_value, 1);
    tcg_gen_andi_tl(target_value, target_value, 0xffff);
    C28X_WRITE_LOC16_RMW(a->loc16, target_value);

    return true;
}

static bool trans_EALLOW(DisasContext* ctx, arg_EALLOW* a) {
    tcg_gen_movi_tl(cpu_sr[EALLOW_FLAG], 1);
    return true;
}

static bool trans_EDIS(DisasContext* ctx, arg_EDIS* a) {
    tcg_gen_movi_tl(cpu_sr[EALLOW_FLAG], 0);
    return true;
}

static bool trans_FLIP_ax(DisasContext* ctx, arg_FLIP_ax* a) {
    // Bit reverse the contents of ax
    //  SWAR divide-and-conquer
    REG_AX_R(b, a->ax);

    TCGv b_left = tcg_temp_new_i32();
    TCGv b_right = tcg_temp_new_i32();

#define SWAR_ROUND(l, r, s)                                                                                            \
    tcg_gen_andi_tl(b_right, b, r);                                                                                    \
    tcg_gen_shri_tl(b_right, b_right, s);                                                                              \
    tcg_gen_andi_tl(b_left, b, l);                                                                                     \
    tcg_gen_shli_tl(b_left, b_left, s);                                                                                \
    tcg_gen_or_tl(b, b_right, b_left);
    // round 1: b = (b & 0xff00) >> 8 | (b & 0x00ff) << 8
    SWAR_ROUND(0xff00, 0x00ff, 8);
    // round 2: b = (b & 0xf0f0) >> 4 | (b & 0x0f0f) << 4
    SWAR_ROUND(0xf0f0, 0x0f0f, 4);
    // round 3: b = (b & 0xcccc) >> 2 | (b & 0x3333) << 2
    SWAR_ROUND(0xcccc, 0x3333, 2);
    // round 4: b = (b & 0xaaaa) >> 1 | (b & 0x5555) << 1
    SWAR_ROUND(0xaaaa, 0x5555, 1);
#undef SWAR_ROUND

    // write back
    REG_AX_W(b, a->ax);

    return true;
}

static bool trans_INC_loc16(DisasContext* ctx, arg_INC_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[V_FLAG], target_value, 0x7fff);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[V_FLAG], target_value, 0x7fff);
    tcg_gen_ext16s_tl(target_value, target_value);
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], target_value, -1);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], target_value, -1);
    tcg_gen_addi_tl(target_value, target_value, 1);
    tcg_gen_andi_tl(target_value, target_value, 0xffff);
    C28X_WRITE_LOC16_RMW(a->loc16, target_value);

    return true;
}

static bool trans_LB_xar7(DisasContext* ctx, arg_LB_xar7* a) {
    // No flags and modes
    TCGv baddr = tcg_temp_new_i32();
    tcg_gen_andi_tl(baddr, cpu_r[C28X_REG_XAR7], 0x3fffff);

    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);

    ctx->base.is_jmp = DISAS_LOOKUP;

    return true;
}

static bool trans_LC_xar7(DisasContext* ctx, arg_LC_xar7* a) {
    // push PC to software stack
    TCGv temp = tcg_temp_new_i32();    // temp(21:0) = PC + 1
    tcg_gen_addi_tl(temp, cpu_r[C28X_REG_PC], 1);
    tcg_gen_andi_tl(temp, temp, 0x3fffff);
    // [SP] = temp(15:0)
    TCGv sp_addr = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_st_tl(temp, sp_addr, 0, MO_16);
    // [SP+1] = temp(21:16)
    tcg_gen_addi_tl(sp_addr, sp_addr, 2);
    tcg_gen_shri_tl(temp, temp, 16);
    tcg_gen_qemu_st_tl(temp, sp_addr, 0, MO_16);
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 2);
    // PC = XAR7
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_XAR7]);
    tcg_gen_andi_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_PC], 0x3fffff);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_LCR_xarn(DisasContext* ctx, arg_LCR_xarn* a) {
    TCGv rpc = tcg_temp_new_i32();
    tcg_gen_andi_tl(rpc, cpu_r[C28X_REG_PC], 0xffff);
    TCGv sp = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_st_tl(rpc, sp, 0, MO_16);
    tcg_gen_shri_tl(rpc, cpu_r[C28X_REG_PC], 16);
    tcg_gen_addi_tl(sp, sp, 2);
    tcg_gen_qemu_st_tl(rpc, sp, 0, MO_16);
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 2);
    tcg_gen_addi_tl(cpu_r[C28X_REG_RPC], cpu_r[C28X_REG_PC], 2);
    tcg_gen_andi_tl(cpu_r[C28X_REG_RPC], cpu_r[C28X_REG_XAR0 + a->xarn], 0x3fffff);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_LPADDR(DisasContext* ctx, arg_LPADDR* a) {
    tcg_gen_movi_tl(cpu_sr[AMODE_FLAG], 1);
    return true;
}

static bool trans_LRET(DisasContext* ctx, arg_LRET* a) {
    // SP = SP - 1
    // temp(31:16) = [SP]
    // SP = SP - 1
    // temp(15:0) = [SP]
    // PC = temp
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    TCGv ret_pc_hi = tcg_temp_new_i32();
    TCGv sp_addr = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(ret_pc_hi, sp_addr, 0, MO_16);
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(cpu_r[C28X_REG_PC], sp_addr, 0, MO_16);
    tcg_gen_shli_tl(ret_pc_hi, ret_pc_hi, 16);
    tcg_gen_or_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_PC], ret_pc_hi);

    return true;
}

static bool trans_LRETE(DisasContext* ctx, arg_LRETE* a) {
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    TCGv ret_pc_hi = tcg_temp_new_i32();
    TCGv sp_addr = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(ret_pc_hi, sp_addr, 0, MO_16);
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(cpu_r[C28X_REG_PC], sp_addr, 0, MO_16);
    tcg_gen_shli_tl(ret_pc_hi, ret_pc_hi, 16);
    tcg_gen_or_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_PC], ret_pc_hi);
    tcg_gen_movi_tl(cpu_sr[INTM_FLAG], 0);
    return true;
}

static bool trans_LRETR(DisasContext* ctx, arg_LRETR* a) {
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_RPC]);
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);

    TCGv ret_pc_hi = tcg_temp_new_i32();
    TCGv sp_addr = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(ret_pc_hi, sp_addr, 0, MO_16);
    tcg_gen_subi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 1);
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_ld_tl(cpu_r[C28X_REG_RPC], sp_addr, 0, MO_16);
    tcg_gen_shli_tl(ret_pc_hi, ret_pc_hi, 16);
    tcg_gen_or_tl(cpu_r[C28X_REG_RPC], cpu_r[C28X_REG_RPC], ret_pc_hi);

    return true;
}

static bool trans_LSL_acc_shft(DisasContext* ctx, arg_LSL_acc_shft* a) {
    TCGv shft = tcg_constant_tl(a->shft);
    LSL_TARGET_SHFT(cpu_r[C28X_REG_ACC], shft);
    LSL_TARGET_FLAG_TEST(cpu_r[C28X_REG_ACC]);
    return true;
}

static bool trans_LSL_acc_t(DisasContext* ctx, arg_LSL_acc_t* a) {
    REG_T(shft, 4);
    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    LSL_TARGET_SHFT(cpu_r[C28X_REG_ACC], shft);
    ENDIF(shft_eqz)
    LSL_TARGET_FLAG_TEST(cpu_r[C28X_REG_ACC]);
    return true;
}

static bool trans_LSL_ax_shft(DisasContext* ctx, arg_LSL_ax_shft* a) {
    REG_AX_R(ax, a->ax);
    TCGv value = tcg_temp_new_i32();
    tcg_gen_shli_tl(value, ax, 16);
    tcg_gen_or_tl(value, value, ax);    // duplicate ax so 32-bit LSL will work for 16-bit ax
    TCGv shft = tcg_constant_tl(a->shft);
    LSL_TARGET_SHFT(ax, shft);
    LSL_TARGET_FLAG_TEST(ax);
    tcg_gen_andi_tl(ax, ax, 0xffff);
    REG_AX_W(ax, a->ax);
    return true;
}

static bool trans_LSL_ax_t(DisasContext* ctx, arg_LSL_ax_t* a) {
    REG_AX_R(ax, a->ax);
    REG_T(shft, 4);
    TCGv value = tcg_temp_new_i32();
    tcg_gen_shli_tl(value, ax, 16);
    tcg_gen_or_tl(value, value, ax);    // duplicate ax so 32-bit LSL will work for 16-bit ax

    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    LSL_TARGET_SHFT(ax, shft);
    ENDIF(shft_eqz)

    LSL_TARGET_FLAG_TEST(ax);
    tcg_gen_andi_tl(ax, ax, 0xffff);
    REG_AX_W(ax, a->ax);
    return true;
}

static bool trans_LSL64_acc_p_shft(DisasContext* ctx, arg_LSL64_acc_p_shft* a) {
    TCGv shft_value = tcg_temp_new_i32();
    tcg_gen_shri_tl(shft_value, cpu_r[C28X_REG_P], 31 - a->shft);
    tcg_gen_shli_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], a->shft + 1);
    tcg_gen_shli_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], a->shft);
    // move c flag
    tcg_gen_shri_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], 1);
    // shft
    tcg_gen_shli_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 1);
    tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft_value);

    CHECK_ACC_P_NZ

    return true;
}

static bool trans_LSL64_acc_p_t(DisasContext* ctx, arg_LSL64_acc_p_t* a) {
    REG_T(shft, 6);
    TCGv r_shft = tcg_constant_tl(31);
    tcg_gen_sub_tl(r_shft, r_shft, shft);

    TCGv shft_value = tcg_temp_new_i32();

    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    tcg_gen_shr_tl(shft_value, cpu_r[C28X_REG_P], r_shft);
    tcg_gen_shl_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], shft);
    tcg_gen_shli_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], 1);
    tcg_gen_shl_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft);
    // move c flag
    tcg_gen_shri_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], 1);
    // shft
    tcg_gen_shli_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 1);
    tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft_value);
    CHECK_ACC_P_NZ
    ENDIF(shft_eqz)

    return true;
}

static bool trans_LSLL_acc_t(DisasContext* ctx, arg_LSLL_acc_t* a) {
    REG_T(shft, 5);

    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    LSL_TARGET_SHFT(cpu_r[C28X_REG_ACC], shft);
    ENDIF(shft_eqz)

    LSL_TARGET_FLAG_TEST(cpu_r[C28X_REG_ACC]);
    return true;
}

static bool trans_LSR_ax_shft(DisasContext* ctx, arg_LSR_ax_shft* a) {
    REG_AX_R(ax, a->ax);
    tcg_gen_shri_tl(ax, ax, a->shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], ax, 1);
    tcg_gen_shri_tl(ax, ax, 1);
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], ax, 0);
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], ax, 0);
    REG_AX_W(ax, a->ax);
    return true;
}

static bool trans_LSR_ax_t(DisasContext* ctx, arg_LSR_ax_t* a) {
    REG_AX_R(ax, a->ax);
    REG_T(shft, 4);

    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    tcg_gen_shr_tl(ax, ax, shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], ax, 1);
    tcg_gen_shri_tl(ax, ax, 1);
    ENDIF(shft_eqz)

    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], ax, 0);
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], ax, 0);
    REG_AX_W(ax, a->ax);
    return true;
}

static bool trans_LSR64_acc_p_shft(DisasContext* ctx, arg_LSR64_acc_p_shft* a) {
    TCGv shft_value = tcg_temp_new_i32();
    tcg_gen_andi_tl(shft_value, cpu_r[C28X_REG_ACC], (2 << a->shft) - 1);    // a->shft + 1
    // move shft_value to MSB
    tcg_gen_shli_tl(shft_value, shft_value, 31 - a->shft);
    tcg_gen_shri_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], a->shft + 1);
    tcg_gen_shri_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], a->shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_P], 1);
    tcg_gen_shri_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], 1);
    tcg_gen_or_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], shft_value);

    CHECK_ACC_P_NZ

    return true;
}

static bool trans_LSR64_acc_p_t(DisasContext* ctx, arg_LSR64_acc_p_t* a) {
    TCGv shft_value = tcg_temp_new_i32();
    REG_T(shft, 6);

    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    TCGv shft_mask = tcg_temp_new_i32();
    tcg_gen_shl_tl(shft_mask, tcg_constant_tl(2), shft);
    tcg_gen_subi_tl(shft_mask, shft_mask, 1);
    TCGv r_shft = tcg_constant_tl(31);
    tcg_gen_sub_tl(r_shft, r_shft, shft);

    tcg_gen_and_tl(shft_value, cpu_r[C28X_REG_ACC], shft_mask);    // a->shft + 1
    // move shft_value to MSB
    tcg_gen_shl_tl(shft_value, shft_value, r_shft);
    tcg_gen_shr_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft);
    tcg_gen_shri_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 1);

    tcg_gen_shr_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_P], 1);
    tcg_gen_shri_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], 1);
    tcg_gen_or_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], shft_value);

    CHECK_ACC_P_NZ
    ENDIF(shft_eqz)
    return true;
}

static bool trans_LSRL_acc_t(DisasContext* ctx, arg_LSRL_acc_t* a) {
    REG_T(shft, 5);
    IF_CONDi(shft_eqz, TCG_COND_EQ, shft, 0)
    clear_c_flag;
    ELSE(shft_eqz)
    tcg_gen_subi_tl(shft, shft, 1);
    tcg_gen_shr_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], shft);
    tcg_gen_andi_tl(cpu_sr[C_FLAG], cpu_r[C28X_REG_ACC], 1);
    tcg_gen_shri_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 1);
    ENDIF(shft_eqz)
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], cpu_r[C28X_REG_ACC], 0);
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], cpu_r[C28X_REG_ACC], 0);
    return true;
}

static bool trans_MOV_acc_loc16(DisasContext* ctx, arg_MOV_acc_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    SXM_EXTEND(target_value);
    tcg_gen_mov_tl(cpu_r[C28X_REG_ACC], target_value);

    gen_set_n_flag(target_value);
    gen_set_z_flag(target_value);
    return true;
}

static bool trans_SETC_mode(DisasContext* ctx, arg_SETC_mode* a) {
    C28X_SETC_MODE(cpu_sr, a->mode);

    return true;
}

static bool trans_SETC_xf(DisasContext* ctx, arg_SETC_xf* a) {
    tcg_gen_movi_tl(cpu_sr[XF_FLAG], 1);
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
    TCGv imm16 = tcg_temp_new_i32();
    TCGv shift = tcg_temp_new_i32();
    tcg_gen_movi_i32(imm16, a->imm16);
    tcg_gen_movi_i32(shift, a->shft);

    ADD_TO_ACC_WITH_FLAGS(imm16, shift)

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

    ADD_TO_ACC_WITH_FLAGS(target_value, t)

    return true;
}

static bool trans_ADD_acc_loc16_shft(DisasContext* ctx, arg_ADD_acc_loc16_shft* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv shift = tcg_constant_i32(a->shft);

    ADD_TO_ACC_WITH_FLAGS(target_value, shift)

    return true;
}

static bool trans_ADD_loc16_s16(DisasContext* ctx, arg_ADD_loc16_s16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);
    TCGv imm16 = tcg_constant_i32(a->imm16s);

    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    TCGv add_sum = tcg_temp_new_i32();

    tcg_gen_ext16s_tl(adder_1, target_value);
    tcg_gen_ext16s_tl(adder_2, imm16);
    tcg_gen_add_tl(add_sum, adder_1, adder_2);

    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], add_sum, 0);
    tcg_gen_setcondi_tl(TCG_COND_LT, cpu_sr[N_FLAG], add_sum, 0);
    watch_for_carry(add_sum, adder_1);

    TCGv store_value = tcg_temp_new_i32();
    tcg_gen_andi_tl(store_value, add_sum, 0xffff);
    C28X_WRITE_LOC16_RMW(a->loc16, store_value);

    TCGv overflow_1 = tcg_temp_new_i32();
    tcg_gen_xor_tl(overflow_1, adder_1, adder_2);
    tcg_gen_not_tl(overflow_1, overflow_1);
    TCGv overflow_2 = tcg_temp_new_i32();
    tcg_gen_xor_tl(overflow_2, add_sum, adder_1);
    tcg_gen_and_tl(cpu_sr[V_FLAG], overflow_1, overflow_2);

    return true;
}

static bool trans_ADDL_loc32_acc(DisasContext* ctx, arg_ADDL_loc32_acc* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC32_RMW(a->loc32, target_value);

    TCGv adder_1 = tcg_temp_new_i32();
    TCGv adder_2 = tcg_temp_new_i32();
    TCGv add_sum = tcg_temp_new_i32();

    tcg_gen_mov_tl(adder_1, target_value);
    tcg_gen_mov_tl(adder_2, cpu_r[C28X_REG_ACC]);
    tcg_gen_add_tl(add_sum, adder_1, adder_2);

    watch_for_carry(add_sum, adder_1);
    watch_for_overflow(add_sum, adder_1, adder_2, OP_ADD_I32);
    gen_set_z_flag(add_sum);
    gen_set_n_flag(add_sum);
    C28X_WRITE_LOC32_RMW(a->loc32, add_sum);

    return true;
}

static bool trans_ADDUL_p_loc32(DisasContext* ctx, arg_ADDUL_p_loc32* a) {
    // P = P + [loc32]
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC32(a->loc32, target_value);
    // treat these as unsigned, so overflow is carry
    tcg_gen_add_tl(cpu_r[C28X_REG_P], cpu_r[C28X_REG_P], target_value);

    watch_for_carry(cpu_r[C28X_REG_P], target_value);
    tcg_gen_mov_tl(cpu_sr[V_FLAG], cpu_sr[C_FLAG]);
    gen_set_n_flag(cpu_r[C28X_REG_P]);
    gen_set_z_flag(cpu_r[C28X_REG_P]);
    tcg_gen_add_tl(cpu_sr[OVC_FLAG], cpu_sr[OVC_FLAG], cpu_sr[V_FLAG]);

    return true;
}

static bool trans_AND_acc_imm16_shft(DisasContext* ctx, arg_AND_acc_imm16_shft* a) {
    TCGv mask = tcg_constant_tl(a->imm16);
    tcg_gen_shli_tl(mask, mask, a->shft);
    gen_and_dst(cpu_r[C28X_REG_ACC], mask, true);

    return true;
}

static bool trans_AND_acc_imm16_shft16(DisasContext* ctx, arg_AND_acc_imm16_shft16* a) {
    TCGv mask = tcg_constant_tl(a->imm16);
    tcg_gen_shli_tl(mask, mask, 16);
    gen_and_dst(cpu_r[C28X_REG_ACC], mask, true);

    return true;
}

static bool trans_AND_ax_loc16_imm16(DisasContext* ctx, arg_AND_ax_loc16_imm16* a) {
    // AX = [loc16] AND 16bit
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    tcg_gen_andi_tl(target_value, target_value, a->imm16);

    if (a->ax == 1) {
        // AH
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0x0000ffff);
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], target_value);
    } else {
        // AL
        tcg_gen_andi_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], 0xffff0000);
        tcg_gen_or_tl(cpu_r[C28X_REG_ACC], cpu_r[C28X_REG_ACC], target_value);
    }
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], target_value, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], target_value, 15);

    return true;
}

static bool trans_AND_loc16_imm16s(DisasContext* ctx, arg_AND_loc16_imm16s* a) {
    // [loc16] = [loc16] AND 16bit
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16_RMW(a->loc16, target_value);
    tcg_gen_andi_tl(target_value, target_value, a->imm16s);
    C28X_WRITE_LOC16_RMW(a->loc16, target_value);

    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], target_value, 0);
    tcg_gen_shri_tl(cpu_sr[N_FLAG], target_value, 15);

    return true;
}

static bool trans_B_offset16_cond(DisasContext* ctx, arg_B_offset16_cond* a) {
    TCGv cond = tcg_temp_new_i32();
    c28x_gen_test_condition(a->cond, cond, cpu_sr);
    TCGv baddr = tcg_constant_tl(a->offset16);
    tcg_gen_ext16s_tl(baddr, baddr);
    tcg_gen_add_tl(baddr, baddr, cpu_r[C28X_REG_PC]);

    tcg_gen_andi_tl(baddr, baddr, 0x3FFFFF);    // 22 bits PC mask

    IF_CONDi(b_set, TCG_COND_EQ, cond, 1)
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    gen_goto_tb(ctx, 0, ctx->pc + (int16_t)a->offset16);
    ELSE(b_set)
    SKIP()
    ENDIF(b_set)

    ctx->base.is_jmp = DISAS_CHAIN;

    return true;
}

static bool trans_BANZ_offset16_arn(DisasContext* ctx, arg_BANZ_offset16_arn* a) {
    TCGv baddr = tcg_constant_tl(a->offset16);
    tcg_gen_ext16s_tl(baddr, baddr);
    tcg_gen_add_tl(baddr, baddr, cpu_r[C28X_REG_PC]);
    tcg_gen_andi_tl(baddr, baddr, 0x3FFFFF);    // 22 bits PC mask

    TCGv arn = tcg_temp_new_i32();
    tcg_gen_mov_tl(arn, cpu_r[C28X_REG_XAR0 + a->arn]);
    tcg_gen_andi_tl(arn, arn, 0xffff);

    TCGv flag = tcg_temp_new_i32();
    tcg_gen_setcondi_tl(TCG_COND_NE, flag, arn, 0);

    tcg_gen_andi_tl(cpu_r[C28X_REG_XAR0 + a->arn], cpu_r[C28X_REG_XAR0 + a->arn], 0xffff0000);
    tcg_gen_subi_tl(arn, arn, 1);
    tcg_gen_andi_tl(arn, arn, 0xffff);
    tcg_gen_or_tl(cpu_r[C28X_REG_XAR0 + a->arn], cpu_r[C28X_REG_XAR0 + a->arn], arn);

    IF_CONDi(b_set, TCG_COND_EQ, flag, 1)
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    gen_goto_tb(ctx, 0, ctx->pc + (int16_t)a->offset16);
    ELSE(b_set)
    SKIP()
    ENDIF(b_set)

    ctx->base.is_jmp = DISAS_CHAIN;

    return true;
}

static bool trans_BAR_offset16_arn_arm_eq(DisasContext* ctx, arg_BAR_offset16_arn_arm_eq* a) {
    TCGv baddr = tcg_constant_tl(a->offset16);
    tcg_gen_ext16s_tl(baddr, baddr);
    tcg_gen_add_tl(baddr, baddr, cpu_r[C28X_REG_PC]);
    tcg_gen_andi_tl(baddr, baddr, 0x3FFFFF);    // 22 bits PC mask

    TCGLabel* label_end = gen_new_label();

    tcg_gen_brcond_tl(TCG_COND_EQ, cpu_r[C28X_REG_XAR0 + a->arn], cpu_r[C28X_REG_XAR0 + a->arm], label_end);
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    gen_goto_tb(ctx, 0, ctx->pc + (int16_t)a->offset16);
    gen_set_label(label_end);

    return true;
}

static bool trans_BAR_offset16_arn_arm_ne(DisasContext* ctx, arg_BAR_offset16_arn_arm_ne* a) {
    TCGv baddr = tcg_constant_tl(a->offset16);
    tcg_gen_ext16s_tl(baddr, baddr);
    tcg_gen_add_tl(baddr, baddr, cpu_r[C28X_REG_PC]);
    tcg_gen_andi_tl(baddr, baddr, 0x3FFFFF);    // 22 bits PC mask

    TCGLabel* label_end = gen_new_label();

    tcg_gen_brcond_tl(TCG_COND_NE, cpu_r[C28X_REG_XAR0 + a->arn], cpu_r[C28X_REG_XAR0 + a->arm], label_end);
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    gen_goto_tb(ctx, 0, ctx->pc + (int16_t)a->offset16);
    gen_set_label(label_end);

    return true;
}

static bool trans_BF_offset16_cond(DisasContext* ctx, arg_BF_offset16_cond* a) {
    // treat this as B
    TCGv cond = tcg_temp_new_i32();
    c28x_gen_test_condition(a->cond, cond, cpu_sr);
    TCGv baddr = tcg_constant_tl(a->offset16);
    tcg_gen_ext16s_tl(baddr, baddr);
    tcg_gen_add_tl(baddr, baddr, cpu_r[C28X_REG_PC]);

    tcg_gen_andi_tl(baddr, baddr, 0x3FFFFF);    // 22 bits PC mask

    IF_CONDi(b_set, TCG_COND_EQ, cond, 1)
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);
    gen_goto_tb(ctx, 0, ctx->pc + (int16_t)a->offset16);
    ELSE(b_set)
    SKIP()
    ENDIF(b_set)

    ctx->base.is_jmp = DISAS_CHAIN;

    return true;
}

static bool trans_CMP_loc16_imm16s(DisasContext* ctx, arg_CMP_loc16_imm16s* a) {
    TCGv loc_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, loc_value);
    TCGv imm16s = tcg_constant_tl(a->imm16s);
    TCGv result = tcg_temp_new_i32();
    // signed expand to 32bit
    tcg_gen_ext16s_tl(loc_value, loc_value);
    tcg_gen_ext16s_tl(imm16s, imm16s);
    tcg_gen_sub_tl(result, loc_value, imm16s);
    // set c flag when no borrow
    tcg_gen_setcond_tl(TCG_COND_GE, cpu_sr[C_FLAG], loc_value, imm16s);
    // set z flag when result is 0
    tcg_gen_setcondi_tl(TCG_COND_EQ, cpu_sr[Z_FLAG], result, 0);
    // set n flag when result is negative
    tcg_gen_setcond_tl(TCG_COND_LT, cpu_sr[N_FLAG], result, 0);
    return true;
}

static bool trans_FFC_xar7_imm22(DisasContext* ctx, arg_FFC_xar7_imm22* a) {
    TCGv baddr = tcg_temp_new_i32();
    tcg_gen_movi_tl(baddr, a->imm22);
    tcg_gen_andi_tl(baddr, baddr, 0x3fffff);
    TCGv xar7 = tcg_temp_new_i32();
    tcg_gen_addi_tl(xar7, cpu_r[C28X_REG_PC], 2);
    tcg_gen_andi_tl(xar7, xar7, 0x3fffff);
    tcg_gen_mov_tl(cpu_r[C28X_REG_XAR7], xar7);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_LB_imm22(DisasContext* ctx, arg_LB_imm22* a) {
    TCGv baddr = tcg_temp_new_i32();
    tcg_gen_movi_tl(baddr, a->imm22);
    tcg_gen_andi_tl(baddr, baddr, 0x3fffff);
    tcg_gen_mov_tl(cpu_r[C28X_REG_PC], baddr);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_LC_imm22(DisasContext* ctx, arg_LC_imm22* a) {
    // push PC to software stack
    TCGv temp = tcg_temp_new_i32();    // temp(21:0) = PC + 1
    tcg_gen_addi_tl(temp, cpu_r[C28X_REG_PC], 1);
    tcg_gen_andi_tl(temp, temp, 0x3fffff);
    // [SP] = temp(15:0)
    TCGv sp_addr = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp_addr, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_st_tl(temp, sp_addr, 0, MO_16);
    // [SP+1] = temp(21:16)
    tcg_gen_addi_tl(sp_addr, sp_addr, 2);
    tcg_gen_shri_tl(temp, temp, 16);
    tcg_gen_qemu_st_tl(temp, sp_addr, 0, MO_16);
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 2);
    // PC = imm22
    tcg_gen_movi_tl(cpu_r[C28X_REG_PC], a->imm22);
    tcg_gen_andi_tl(cpu_r[C28X_REG_PC], cpu_r[C28X_REG_PC], 0x3fffff);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_LCR_imm22(DisasContext* ctx, arg_LCR_imm22* a) {
    TCGv rpc = tcg_temp_new_i32();
    tcg_gen_andi_tl(rpc, cpu_r[C28X_REG_PC], 0xffff);
    TCGv sp = tcg_temp_new_i32();
    tcg_gen_muli_tl(sp, cpu_r[C28X_REG_SP], 2);
    tcg_gen_qemu_st_tl(rpc, sp, 0, MO_16);
    tcg_gen_shri_tl(rpc, cpu_r[C28X_REG_PC], 16);
    tcg_gen_addi_tl(sp, sp, 2);
    tcg_gen_qemu_st_tl(rpc, sp, 0, MO_16);
    tcg_gen_addi_tl(cpu_r[C28X_REG_SP], cpu_r[C28X_REG_SP], 2);
    tcg_gen_addi_tl(cpu_r[C28X_REG_RPC], cpu_r[C28X_REG_PC], 2);
    tcg_gen_movi_tl(cpu_r[C28X_REG_PC], a->imm22);

    ctx->base.is_jmp = DISAS_LOOKUP;
    return true;
}

static bool trans_MOV_addr16_loc16(DisasContext* ctx, arg_MOV_addr16_loc16* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);
    TCGv addr16 = tcg_constant_i32(a->addr16);
    tcg_gen_muli_tl(addr16, addr16, 2);
    tcg_gen_qemu_st_tl(target_value, addr16, 0, MO_16);

    return true;
}

static bool trans_MOV_acc_imm16_shft(DisasContext* ctx, arg_MOV_acc_imm16_shft* a) {
    TCGv imm = tcg_constant_i32(a->imm16);

    SXM_EXTEND(imm)

    tcg_gen_shli_tl(imm, imm, a->shft);
    tcg_gen_mov_tl(cpu_r[C28X_REG_ACC], imm);

    gen_set_z_flag(cpu_r[C28X_REG_ACC]);
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);

    return true;
}

static bool trans_MOV_acc_loc16_t(DisasContext* ctx, arg_MOV_acc_loc16_t* a) {
    TCGv target_value = tcg_temp_new_i32();
    C28X_READ_LOC16(a->loc16, target_value);

    SXM_EXTEND(target_value)

    tcg_gen_mov_i32(cpu_r[C28X_REG_ACC], target_value);

    gen_set_z_flag(cpu_r[C28X_REG_ACC]);
    gen_set_n_flag(cpu_r[C28X_REG_ACC]);

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
    ctx->pc = ctx->base.pc_first / 2;
}

static void c28x_tr_tb_start(DisasContextBase* dcbase, CPUState* cs) {}

static void c28x_tr_tb_stop(DisasContextBase* dcbase, CPUState* cs) {
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    switch (ctx->base.is_jmp) {
    case DISAS_NEXT:
    case DISAS_TOO_MANY:
    case DISAS_CHAIN:
        gen_goto_tb(ctx, 1, ctx->pc);
        tcg_gen_movi_tl(cpu_r[C28X_REG_PC], ctx->pc);
        /* fall through */
    case DISAS_LOOKUP:
    case DISAS_EXIT:
        // tcg_gen_exit_tb(NULL, 0);
        tcg_gen_lookup_and_goto_ptr();
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
    tcg_gen_insn_start(ctx->pc);
}

static void c28x_tr_translate_insn(DisasContextBase* dcbase, CPUState* cs) {
    DisasContext* ctx = container_of(dcbase, DisasContext, base);
    uint16_t opcode16;

    // load first 16-bits for decoding
    opcode16 = cpu_lduw_be_data(ctx->env, ctx->pc * 2);

    if (!decode_insn16(ctx, opcode16)) {
        // load next 16-bits for decoding
        uint32_t opcode32 = cpu_lduw_be_data(ctx->env, ctx->pc * 2 + 2) | (opcode16 << 16);
        if (!decode_insn32(ctx, opcode32)) {
            error_report("[C28X-TCG] c28x_tr_translate_insn: unknown instruction, pc: 0x%x", ctx->pc);
            error_report("[C28X-TCG] c28x_tr_translate_insn: opcode16: 0x%04x, opcode32: 0x%08x", opcode16, opcode32);
            gen_helper_raise_illegal_instruction(tcg_env);

            ctx->base.is_jmp = DISAS_NORETURN;
            return;
        } else {
            // legal 32-bit instruction
            ctx->pc += 2;
        }
    } else {
        // legal 16-bit instruction
        ctx->pc += 1;
    }
    ctx->base.pc_next = ctx->pc * 2;
}

static bool c28x_tr_disas_log(const DisasContextBase* dcbase, CPUState* cs, FILE* log_file) {
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
    // base->pc_first should be the actual address
    // in C28x, one byte is 16-bits wide, so we need to multiply by 2
    // ctx->pc is the address of guest, which C28X_REG_PC holds
    translator_loop(cs, tb, max_insns, pc, host_pc, &c28x_tr_ops, &dc.base);
}