#include "mode-flags.h"

static const char* c28x_mode_flags_names[] = {"SXM", "OVM", "TC", "C", "INTM", "DBGM", "PAGE0", "VMAP"};

void c28x_gen_set_mode_flag(TCGv cpu_sr[], uint8_t mask, int set) {
    TCGv value = tcg_constant_tl(set);

    for (int i = 0; i < 8; i++) {
        if ((mask & c28x_mode_flags[i]) != 0) {
            tcg_gen_mov_tl(cpu_sr[c28_mode_cpu_sr_idx[i]], value);
        }
    }
}

char* c28x_parse_mode_flag(uint8_t mask) {
    static char buf[64] = {0};
    memset(buf, 0, 64);

    for (int i = 0; i < 8; i++) {
        if ((mask & c28x_mode_flags[i]) != 0) {
            strcat(buf, c28x_mode_flags_names[i]);
            strcat(buf, ",");
        }
    }

    // remove the last comma, we may not assume that clrc always set some flags
    if (strlen(buf) > 0) {
        buf[strlen(buf) - 1] = 0;
    }

    return buf;
}

void c28x_pack_status_reg_0(TCGv dst, TCGv cpu_sr[]) {
    tcg_gen_movi_tl(dst, 0);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[OVC_FLAG], 10, 6);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[PM_FLAG], 7, 3);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[V_FLAG], 6, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[N_FLAG], 5, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[Z_FLAG], 4, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[C_FLAG], 3, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[TC_FLAG], 2, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[OVM_FLAG], 1, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[SXM_FLAG], 0, 1);
}

void c28x_unpack_status_reg_0(TCGv cpu_sr[], TCGv value) {
    tcg_gen_extract_tl(cpu_sr[OVC_FLAG], value, 10, 6);
    tcg_gen_extract_tl(cpu_sr[PM_FLAG], value, 7, 3);
    tcg_gen_extract_tl(cpu_sr[V_FLAG], value, 6, 1);
    tcg_gen_extract_tl(cpu_sr[N_FLAG], value, 5, 1);
    tcg_gen_extract_tl(cpu_sr[Z_FLAG], value, 4, 1);
    tcg_gen_extract_tl(cpu_sr[C_FLAG], value, 3, 1);
    tcg_gen_extract_tl(cpu_sr[TC_FLAG], value, 2, 1);
    tcg_gen_extract_tl(cpu_sr[OVM_FLAG], value, 1, 1);
    tcg_gen_extract_tl(cpu_sr[SXM_FLAG], value, 0, 1);
}

void c28x_pack_status_reg_1(TCGv dst, TCGv cpu_sr[]) {
    tcg_gen_movi_tl(dst, 0);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[ARP_FLAG], 13, 3);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[XF_FLAG], 12, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[M0M1MAP_FLAG], 11, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[OBJMODE_FLAG], 9, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[AMODE_FLAG], 8, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[IDLESTAT_FLAG], 7, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[EALLOW_FLAG], 6, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[LOOP_FLAG], 5, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[SPA_FLAG], 4, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[VMAP_FLAG], 3, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[PAGE0_FLAG], 2, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[DBGM_FLAG], 1, 1);
    tcg_gen_deposit_tl(dst, dst, cpu_sr[INTM_FLAG], 0, 1);
}

void c28x_unpack_status_reg_1(TCGv cpu_sr[], TCGv value) {
    tcg_gen_extract_tl(cpu_sr[ARP_FLAG], value, 13, 3);
    tcg_gen_extract_tl(cpu_sr[XF_FLAG], value, 12, 1);
    tcg_gen_extract_tl(cpu_sr[M0M1MAP_FLAG], value, 11, 1);
    tcg_gen_extract_tl(cpu_sr[OBJMODE_FLAG], value, 9, 1);
    tcg_gen_extract_tl(cpu_sr[AMODE_FLAG], value, 8, 1);
    tcg_gen_extract_tl(cpu_sr[IDLESTAT_FLAG], value, 7, 1);
    tcg_gen_extract_tl(cpu_sr[EALLOW_FLAG], value, 6, 1);
    tcg_gen_extract_tl(cpu_sr[LOOP_FLAG], value, 5, 1);
    tcg_gen_extract_tl(cpu_sr[SPA_FLAG], value, 4, 1);
    tcg_gen_extract_tl(cpu_sr[VMAP_FLAG], value, 3, 1);
    tcg_gen_extract_tl(cpu_sr[PAGE0_FLAG], value, 2, 1);
    tcg_gen_extract_tl(cpu_sr[DBGM_FLAG], value, 1, 1);
    tcg_gen_extract_tl(cpu_sr[INTM_FLAG], value, 0, 1);
}