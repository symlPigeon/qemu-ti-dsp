#include "mode-flags.h"

static const char* c28x_mode_flags_names[] = {"SXM", "OVM", "TC", "C", "INTM", "DBGM", "PAGE0", "VMAP"};

void c28_gen_set_mode_flag(TCGv cpu_sr[], uint8_t mask, int set) {
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