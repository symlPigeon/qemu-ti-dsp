#include "qemu/osdep.h"

#include "address-mode.h"
#include "condition.h"
#include "cpu.h"

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

INSN(ABS_acc, ABS, "ACC")
INSN(ABSTC_acc, ABSTC, "ACC")

INSN(ADD_acc_imm16_shft, ADD, "ACC, #0x%x << #%d", a->imm16, a->shft)
INSN(ADD_acc_loc16_t, ADD, "ACC, %s << T", LOC(a->loc16))
INSN(ADD_acc_loc16, ADD, "ACC, %s", LOC(a->loc16))
INSN(ADD_acc_loc16_shft, ADD, "ACC, %s << #%d", LOC(a->loc16), a->shft)
INSN(ADD_acc_loc16_shl16, ADD, "ACC, %s << #16", LOC(a->loc16))
INSN(ADD_ax_loc16, ADD, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(ADD_loc16_ax, ADD, "%s, %s", LOC(a->loc16), AX(a->ax))
INSN(ADD_loc16_s16, ADD, "%s, #%hd", LOC(a->loc16), a->imm16s)
INSN(ADD_acc_imm8, ADD, "ACC, #%0x02x", a->imm8)
INSN(ADDB_ax_imm8s, ADDB, "%s, #%hd", AX(a->ax), a->imm8s)
INSN(ADDB_sp_imm7, ADDB, "SP, #%d", a->imm7)
INSN(ADDB_xarn_7bit, ADDB, "%s, 0x%x", XARn(a->xarn), a->imm7)
INSN(ADDCU_acc_loc16, ADDCU, "ACC, %s", LOC(a->loc16))
INSN(ADDL_acc_loc32, ADDL, "ACC, %s", LOC(a->loc32))
INSN(ADDL_loc32_acc, ADDL, "%s, ACC", LOC(a->loc32))
INSN(ADDU_acc_loc16, ADDU, "ACC, %s", LOC(a->loc16))
INSN(ADDUL_p_loc32, ADDUL, "P, %s", LOC(a->loc32))
INSN(ADRK_imm8, ADRK, "#0x%02x", a->imm8)

INSN(AND_acc_imm16_shft, AND, "ACC, #0x%04x << #%d", a->imm16, a->shft)
INSN(AND_acc_imm16_shft16, AND, "ACC, #0x%04x << #16", a->imm16)
INSN(AND_acc_loc16, AND, "ACC, %s", LOC(a->loc16))
INSN(AND_ax_loc16_imm16, AND, "%s, %s, #0x%04x", AX(a->ax), LOC(a->loc16), a->imm16)
INSN(AND_loc16_ax, AND, "%s, %s", LOC(a->loc16), AX(a->ax))
INSN(AND_ax_loc16, AND, "%s, %s", AX(a->ax), LOC(a->loc16))
INSN(AND_loc16_imm16s, AND, "%s, #0x%04x", LOC(a->loc16), a->imm16s)
INSN(AND_ax_imm8s, AND, "%s, #0x00%02x", AX(a->ax), a->imm8s)

INSN(ASP, ASP, "")

INSN(ASR_ax_shft, ASR, "%s, #%d", AX(a->ax), a->shft)
INSN(ASR_ax_t, ASR, "%s, T", AX(a->ax))
INSN(ASR64_acc_p_shft, ASR64, "ACC:P, #%d", a->shft)
INSN(ASR64_acc_p_t, ASR64, "ACC:P, T")
INSN(ASRL_acc_t, ASRL, "ACC, T")

INSN(B_offset16_cond, B, "%s, %d", COND(a->cond), a->offset16)

INSN(MOV_acc_loc16_t, MOV, "ACC, %s << T", LOC(a->loc16))
INSN(LB_xar7, LB, "XAR7")
INSN(MOVL_xar0_imm22, MOVL, "XAR0, #0x%x", a->imm22)