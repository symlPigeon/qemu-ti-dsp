#include "qemu/osdep.h"

#include "address-mode.h"
#include "condition.h"
#include "cpu.h"
#include "mode-flags.h"

typedef struct DisasContext {
    // Provided by QEMU
    disassemble_info* dis;

    uint32_t addr;
    uint32_t pc;

    uint8_t bytes[4];
} DisasContext;

/* Include the auto-generated decoder.  */

#include "decode-insn16.c.inc"
#include "decode-insn32.c.inc"

#define output(mnemonic, format, ...)                                                                                  \
    (pctx->dis->fprintf_func(pctx->dis->stream, "%-9s " format, mnemonic, ##__VA_ARGS__))

int c28x_print_insn(bfd_vma addr, disassemble_info* info) {
    DisasContext ctx;
    DisasContext* pctx = &ctx;
    bfd_byte buffer[4];
    int status;

    ctx.dis = info;
    ctx.pc = addr;

    status = info->read_memory_func(addr, buffer, 2, info);
    if (status != 0) {
        info->memory_error_func(status, addr, info);
        return -1;
    }
    uint16_t insn = bfd_getb16(buffer);
    if (decode_insn16(&ctx, insn)) {
        // valid 16-bit instruction
        return 2;
    }
    // try to decode 32-bit instruction
    status = info->read_memory_func(addr, buffer, 4, info);
    if (status != 0) {
        info->memory_error_func(status, addr, info);
        return -1;
    }
    uint32_t insn32 = bfd_getb32(buffer);
    if (decode_insn32(&ctx, insn32)) {
        // valid 32-bit instruction
        return 4;
    }
    // invalid instruction, try to print as .db
    output(".db", "0x%02x", buffer[0]);
    // step 2 bytes
    return 2;
}

void c28x_print_address(bfd_vma addr, struct disassemble_info* info) {
    info->fprintf_func(info->stream, "0x%08" PRIx64 ":  ", addr / 2);
}

#define INSN(opcode, mnemonic, format, ...)                                                                            \
    static bool trans_##opcode(DisasContext* pctx, arg_##opcode* a) {                                                  \
        output(#mnemonic, format, ##__VA_ARGS__);                                                                      \
        return true;                                                                                                   \
    }

#define REG(x)  c28x_cpu_r_names[x]
#define XARn(x) c28x_cpu_r_names[C28X_REG_XAR0 + x]
#define LOC(x)  c28x_parse_loc_desc(x)
#define AX(x)   (x) == 1 ? "AH" : "AL"
#define COND(x) c28x_parse_condition(x)
#define MODE(x) c28x_parse_mode_flag(x)

// ABS instructions
INSN(ABS_acc, ABS, "ACC")
INSN(ABSTC_acc, ABSTC, "ACC")

// Add
INSN(ADD_acc_imm16_shft, ADD, "ACC, #0x%x << #%d", a->imm16, a->shft)
INSN(ADD_acc_loc16_t, ADD, "ACC, %s << T", LOC(a->loc16))
INSN(ADD_acc_loc16, ADD, "ACC, %s", LOC(a->loc16))
INSN(ADD_acc_loc16_shft, ADD, "ACC, %s << #%d", LOC(a->loc16), a->shft)
INSN(ADD_acc_loc16_shl16, ADD, "ACC, %s << #16", LOC(a->loc16))
INSN(ADD_ax_loc16, ADD, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(ADD_loc16_ax, ADD, "%s, %s", LOC(a->loc16), AX(a->ax))
INSN(ADD_loc16_s16, ADD, "%s, #%hd", LOC(a->loc16), a->imm16s)
INSN(ADD_acc_imm8, ADD, "ACC, #0x%02x", a->imm8)
INSN(ADDB_ax_imm8, ADDB, "%s, #%hd", AX(a->ax), a->imm8)
INSN(ADDB_sp_imm7, ADDB, "SP, #%d", a->imm7)
INSN(ADDB_xarn_7bit, ADDB, "%s, 0x%x", XARn(a->xarn), a->imm7)
INSN(ADDCU_acc_loc16, ADDCU, "ACC, %s", LOC(a->loc16))
INSN(ADDL_acc_loc32, ADDL, "ACC, %s", LOC(a->loc32))
INSN(ADDL_loc32_acc, ADDL, "%s, ACC", LOC(a->loc32))
INSN(ADDU_acc_loc16, ADDU, "ACC, %s", LOC(a->loc16))
INSN(ADDUL_p_loc32, ADDUL, "P, %s", LOC(a->loc32))
INSN(ADRK_imm8, ADRK, "#0x%02x", a->imm8)

// AND
INSN(AND_acc_imm16_shft, AND, "ACC, #0x%04x << #%d", a->imm16, a->shft)
INSN(AND_acc_imm16_shft16, AND, "ACC, #0x%04x << #16", a->imm16)
INSN(AND_acc_loc16, AND, "ACC, %s", LOC(a->loc16))
INSN(AND_ax_loc16_imm16, AND, "%s, %s, #0x%04x", AX(a->ax), LOC(a->loc16), a->imm16)
INSN(AND_loc16_ax, AND, "%s, %s", LOC(a->loc16), AX(a->ax))
INSN(AND_ax_loc16, AND, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(AND_loc16_imm16s, AND, "%s, #0x%04x", LOC(a->loc16), a->imm16s)
INSN(AND_ax_imm8, AND, "%s, #0x00%02x", AX(a->ax), a->imm8)

// Align Stack Pointer
INSN(ASP, ASP, "")

// Arithmetic Shift
INSN(ASR_ax_shft, ASR, "%s, #%d", AX(a->ax), a->shft)
INSN(ASR_ax_t, ASR, "%s, T", AX(a->ax))
INSN(ASR64_acc_p_shft, ASR64, "ACC:P, #%d", a->shft)
INSN(ASR64_acc_p_t, ASR64, "ACC:P, T")
INSN(ASRL_acc_t, ASRL, "ACC, T")

// Branch
INSN(B_offset16_cond, B, "%s, %hd", COND(a->cond), (int16_t)a->offset16)
INSN(BANZ_offset16_arn, BANZ, "%hd, AR%d--", (int16_t)a->offset16, a->arn)
INSN(BAR_offset16_arn_arm_eq, BAR, "%hd, AR%d, AR%d, EQ", (int16_t)a->offset16, a->arn, a->arm)
INSN(BAR_offset16_arn_arm_ne, BAR, "%hd, AR%d, AR%d, NEQ", (int16_t)a->offset16, a->arn, a->arm)
INSN(BF_offset16_cond, BF, "%s, %hd", COND(a->cond), (int16_t)a->offset16)

// Control Bit Instructions
INSN(C27MAP, C27MAP, "")
INSN(C27OBJ, C27OBJ, "")
INSN(C28ADDR, C28ADDR, "")
INSN(C28MAP, C28MAP, "")
INSN(C28OBJ, C28OBJ, "")
INSN(CLRC_ovc, CLRC, "OVC")
INSN(CLRC_xf, CLRC, "XF")
INSN(CLRC_mode, CLRC, "%s", MODE(a->mode))

// Compare
INSN(CMP_ax_loc16, CMP, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(CMP_loc16_imm16s, CMP, "%s, #0x%04x", LOC(a->loc16), a->imm16s)
INSN(CMP64_acc_p, CMP, "ACC:P")
INSN(CMPB_ax_imm8, CMPB, "%s, #0x%02x", AX(a->ax), a->imm8)
INSN(CMPL_acc_loc32, CMPL, "ACC, %s", LOC(a->loc32))
INSN(CMPL_acc_p_pm, CMPL, "ACC, P<<PM")
INSN(CMPR0, CMPR, "0")
INSN(CMPR3, CMPR, "3")

// Count Significations Bits
INSN(CSB_acc, CSB, "ACC")

// Decrement
INSN(DEC_loc16, DEC, "%s", LOC(a->loc16))

// Control Access to Sys Regs
INSN(EALLOW, EALLOW, "")
INSN(EDIS, EDIS, "")

// Fast Function Call
INSN(FFC_xar7_imm22, FFC, "XAR7, #0x%x", a->imm22)

// Flip Bits
INSN(FLIP_ax, FLIP, "%s", AX(a->ax))

// Increasement
INSN(INC_loc16, INC, "%s", LOC(a->loc16))

// Long branch / Function Call
INSN(LB_xar7, LB, "*XAR7")
INSN(LB_imm22, LB, "#0x%x", a->imm22)
INSN(LC_xar7, LC, "*XAR7")
INSN(LC_imm22, LC, "#0x%x", a->imm22)
INSN(LCR_imm22, LCR, "#0x%x", a->imm22)
INSN(LCR_xarn, LCR, "%s", XARn(a->xarn))

// Change Address Mode
INSN(LPADDR, LPADDR, "")

// Return
INSN(LRET, LRET, "")
INSN(LRETE, LRETE, "")
INSN(LRETR, LRETR, "")

// Logical Shift
INSN(LSL_acc_shft, LSL, "ACC, #%d", a->shft)
INSN(LSL_acc_t, LSL, "ACC, T")
INSN(LSL_ax_shft, LSL, "%s, #%d", AX(a->ax), a->shft)
INSN(LSL_ax_t, LSL, "%s, T", AX(a->ax))
INSN(LSL64_acc_p_shft, LSL64, "ACC:P, #%d", a->shft)
INSN(LSL64_acc_p_t, LSL64, "ACC:P, T")
INSN(LSLL_acc_t, LSLL, "ACC, T")
INSN(LSR_ax_shft, LSR, "%s, #%d", AX(a->ax), a->shft)
INSN(LSR_ax_t, LSR, "%s, T", AX(a->ax))
INSN(LSR64_acc_p_shft, LSR64, "ACC:P, #%d", a->shft)
INSN(LSR64_acc_p_t, LSR64, "ACC:P, T")
INSN(LSRL_acc_t, LSRL, "ACC, T")

// Move
INSN(MOV_addr16_loc16, MOV, "*(0:0x%04x), %s", a->addr16, LOC(a->loc16))
INSN(MOV_acc_imm16_shft, MOV, "ACC, #0x%04x << #%d", a->imm16, a->shft)
INSN(MOV_acc_loc16_t, MOV, "ACC, %s << T", LOC(a->loc16))
INSN(MOVL_xar0_imm22, MOVL, "XAR0, #0x%x", a->imm22)
INSN(MOV_acc_loc16, MOV, "ACC, %s", LOC(a->loc16))
INSN(MOV_acc_loc16_shft, MOV, "ACC, %s << #%d", LOC(a->loc16), a->shft)
INSN(MOV_acc_loc16_shft16, MOV, "ACC, %s << #16", LOC(a->loc16))
INSN(MOV_ar6_loc16, MOV, "AR6, %s", LOC(a->loc16))
INSN(MOV_ar7_loc16, MOV, "AR7, %s", LOC(a->loc16))
INSN(MOV_ax_loc16, MOV, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(MOV_dp_imm10, MOV, "DP, #0x%x", a->imm10)
INSN(MOV_ier_loc16, MOV, "IER, %s", LOC(a->loc16))
INSN(MOV_loc16_imm16, MOV, "%s, #0x%04x", LOC(a->loc16), a->imm16)
INSN(MOV_loc16_addr16, MOV, "%s, *(0:0x%04x)", LOC(a->loc16), a->addr16)
INSN(MOV_loc16_0, MOV, "%s, #0", LOC(a->loc16))
INSN(MOV_loc16_acc_shft1, MOV, "%s, ACC << #1", LOC(a->loc16))
INSN(MOV_loc16_acc_shft, MOV, "%s, ACC << #%d", LOC(a->loc16), a->shft3)
INSN(MOV_loc16_arn, MOV, "AR%d, %s", a->arn, LOC(a->loc16))
INSN(MOV_loc16_ax, MOV, "%s, %s", LOC(a->loc16), AX(a->ax))
INSN(MOV_loc16_ax_cond, MOV, "%s, %s, %s", LOC(a->loc16), AX(a->ax), COND(a->cond))
INSN(MOV_loc16_ier, MOV, "%s, IER", LOC(a->loc16))
INSN(MOV_loc16_ovc, MOV, "%s, OVC", LOC(a->loc16))
INSN(MOV_loc16_p, MOV, "%s, P", LOC(a->loc16))
INSN(MOV_loc16_t, MOV, "%s, T", LOC(a->loc16))
INSN(MOV_ovc_loc16, MOV, "OVC, %s", LOC(a->loc16))
INSN(MOV_ph_loc16, MOV, "PH, %s", LOC(a->loc16))
INSN(MOV_pl_loc16, MOV, "PL, %s", LOC(a->loc16))
INSN(MOV_pm_ax, MOV, "PM, %s", AX(a->ax))
INSN(MOV_t_loc16, MOV, "T, %s", LOC(a->loc16))
INSN(MOV_tl_0, MOV, "TL, #0")
INSN(MOV_xarn_pc, MOV, "%s, PC", XARn(a->xarn))

INSN(MOVA_t_loc16, MOVA, "T, %s", LOC(a->loc16))
INSN(MOVAD_t_loc16, MOVAD, "T, %s", LOC(a->loc16))

// Byte Move
INSN(MOVB_acc_imm8, MOVB, "ACC, #0x%02x", a->imm8)
INSN(MOVB_ar6_imm8, MOVB, "AR6, #0x%02x", a->imm8)
INSN(MOVB_ar7_imm8, MOVB, "AR7, #0x%02x", a->imm8)
INSN(MOVB_ax_imm8, MOVB, "%s, #0x%02x", AX(a->ax), a->imm8)
INSN(MOVB_loc16_imm8_cond, MOVB, "%s, #0x%02x, %s", LOC(a->loc16), a->imm8, COND(a->cond))
INSN(MOVB_xarn_imm8, MOVB, "%s, #0x%02x", XARn(a->xarn), a->imm8)
INSN(MOVB_xar6_imm8, MOVB, "XAR6, #0x%02x", a->imm8)
INSN(MOVB_xar7_imm8, MOVB, "XAR7, #0x%02x", a->imm8)

INSN(SETC_mode, SETC, "%s", MODE(a->mode))
INSN(SETC_xf, SETC, "XF")