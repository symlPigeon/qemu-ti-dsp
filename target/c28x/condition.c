#include "condition.h"
#include "qemu/log-for-trace.h"

void gen_test_condition(uint8_t cond, TCGv result, TCGv* cpu_sr) {
    switch (cond) {
    case 0x0:
        // NEQ  =>  Z=0
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[Z_FLAG], 0);
        break;
    case 0x1:
        // EQ  =>  Z=1
        tcg_gen_setcondi_tl(TCG_COND_NE, result, cpu_sr[Z_FLAG], 0);
        break;
    case 0x2:
        // GT  =>  Z=0 & N=0
        tcg_gen_or_tl(result, cpu_sr[Z_FLAG], cpu_sr[N_FLAG]);
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, result, 0);
        break;
    case 0x3:
        // GEQ  =>  N=0
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[N_FLAG], 0);
        break;
    case 0x4:
        // LT  =>  N=1
        tcg_gen_setcondi_tl(TCG_COND_NE, result, cpu_sr[N_FLAG], 0);
        break;
    case 0x5:
        // LEQ  =>  Z=1 | N=1
        tcg_gen_or_tl(result, cpu_sr[Z_FLAG], cpu_sr[N_FLAG]);
        tcg_gen_setcondi_tl(TCG_COND_NE, result, result, 0);
        break;
    case 0x6:
        // HI  =>  C=1 & Z=0  Higher?
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[Z_FLAG], 0);
        tcg_gen_and_tl(result, result, cpu_sr[C_FLAG]);
        tcg_gen_setcondi_tl(TCG_COND_NE, result, result, 0);
        break;
    case 0x7:
        // HIS, C  =>  C=1,  Higher or Same, Carry Set
        tcg_gen_setcondi_tl(TCG_COND_NE, result, cpu_sr[C_FLAG], 0);
        break;
    case 0x8:
        // LO, NC  =>  C=0,  Lower, Carry Clear
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[C_FLAG], 0);
        break;
    case 0x9:
        // LOS  =>  C=0 | Z=1, Lower or Same
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[C_FLAG], 0);
        tcg_gen_or_tl(result, result, cpu_sr[Z_FLAG]);
        tcg_gen_setcondi_tl(TCG_COND_NE, result, result, 0);
        break;
    case 0xa:
        // NOV  =>  V=0, No Overflow, if V is tested, then clear V
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[V_FLAG], 0);
        tcg_gen_movi_tl(cpu_sr[V_FLAG], 0);
        break;
    case 0xb:
        // OV  =>  V=1, Overflow, if V is tested, then set V
        tcg_gen_setcondi_tl(TCG_COND_NE, result, cpu_sr[V_FLAG], 0);
        tcg_gen_movi_tl(cpu_sr[V_FLAG], 1);
        break;
    case 0xc:
        // NTC  =>  TC=0
        tcg_gen_setcondi_tl(TCG_COND_EQ, result, cpu_sr[TC_FLAG], 0);
        break;
    case 0xd:
        // TC  =>  TC=1
        tcg_gen_setcondi_tl(TCG_COND_NE, result, cpu_sr[TC_FLAG], 0);
        break;
    case 0xe:
        // NBIO  =>  Not Implemented!
        // FIXME: The NBIO condition requires an external pin that is only present on TMS320x2801x devices.
        qemu_log("NBIO condition is not implemented! Treat as always false!\n");
        break;
    case 0xf:
        // UNC  =>  Unconditional
        tcg_gen_movi_tl(result, 1);
        break;
    default:
        qemu_log("Unknown condition: %d\n", cond);
        break;
    }
}

const char* c28x_parse_condition(uint8_t cond) {
    switch (cond) {
    case 0x0:
        return "NEQ";
    case 0x1:
        return "EQ";
    case 0x2:
        return "GT";
    case 0x3:
        return "GEQ";
    case 0x4:
        return "LT";
    case 0x5:
        return "LEQ";
    case 0x6:
        return "HI";
    case 0x7:
        return "HIS,C";
    case 0x8:
        return "LO,NC";
    case 0x9:
        return "LOS";
    case 0xa:
        return "NOV";
    case 0xb:
        return "OV";
    case 0xc:
        return "NTC";
    case 0xd:
        return "TC";
    case 0xe:
        return "NBIO";
    case 0xf:
        return "UNC";
    default:
        return "UNKNOWN";
    }
}