#include "qemu/osdep.h"

#include "cpu.h"

typedef struct DisasContext {
    // Provided by QEMU
    disassemble_info* dis;

    uint32_t addr;
    uint32_t pc;

    uint8_t bytes[4];
} DisasContext;

/* Include the auto-generated decoder.  */
static bool decode_insn(DisasContext* ctx, uint32_t insn);
#include "decode-insn16.c.inc"
#include "decode-insn32.c.inc"

#define output(mnemonic, format, ...)                                                                                  \
    (pctx->dis->fprintf_func(pctx->dis->stream, "%-9s " format, mnemonic, ##__VA_ARGS__))

#define INSN(opcode, mnemonic, format, ...)                                                                            \
    static bool trans_##opcode(DisasContext* pctx, arg_##opcode* a) {                                                  \
        output(#mnemonic, format, ##__VA_ARGS__);                                                                      \
        return true;                                                                                                   \
    }

#define REG(x)  c28x_cpu_r_names[x]
#define XARn(x) c28x_cpu_r_names[C28X_REG_XAR0 + x]

INSN(ABS_acc, ABS, "ACC")
INSN(ABSTC_acc, ABSTC, "ACC")
INSN(ADD_acc_imm16_shft, "ADD", "ACC, #%d << #%d", a->imm16, a->shft)
INSN(ADDB_xarn_7bit, ADDB, "%s, %d", XARn(a->xarn), a->imm7)
INSN(LB_xar7, LB, "")
INSN(MOVL_xar0_imm22, MOVL, "%d", a->imm22)