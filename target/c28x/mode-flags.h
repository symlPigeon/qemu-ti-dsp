#ifndef C28X_CPU_MODE_FLAGS_H
#define C28X_CPU_MODE_FLAGS_H

#include "qemu/osdep.h"

#include "cpu.h"
#include "tcg/tcg-op.h"
#include "tcg/tcg.h"

#define SXM_MODE_MASK   (1 << 0)
#define OVM_MODE_MASK   (1 << 1)
#define TC_MODE_MASK    (1 << 2)
#define C_MODE_MASK     (1 << 3)
#define INTM_MODE_MASK  (1 << 4)
#define DBGM_MODE_MASK  (1 << 5)
#define PAGE0_MODE_MASK (1 << 6)
#define VMAP_MODE_MASK  (1 << 7)

static const uint8_t c28x_mode_flags[] = {SXM_MODE_MASK,  OVM_MODE_MASK,  TC_MODE_MASK,    C_MODE_MASK,
                                          INTM_MODE_MASK, DBGM_MODE_MASK, PAGE0_MODE_MASK, VMAP_MODE_MASK};
static const uint32_t c28_mode_cpu_sr_idx[] = {SXM_FLAG,  OVM_FLAG,  TC_FLAG,    C_FLAG,
                                               INTM_FLAG, DBGM_FLAG, PAGE0_FLAG, VMAP_FLAG};

/**
 * Sets or clears a mode flag in the CPU status register.
 *
 * @param cpu_sr An array representing the CPU status register.
 * @param mask A bitmask indicating which flag(s) to modify.
 * @param set A boolean value indicating whether to set (1) or clear (0) the flag(s).
 */
void c28_gen_set_mode_flag(TCGv cpu_sr[], uint8_t mask, int set);

/**
 * Parses the given mode flag mask and returns a string representation of the mode.
 *
 * @param mask The mode flag mask to parse.
 * @return A string representation of the mode corresponding to the given mask.
 */
char* c28x_parse_mode_flag(uint8_t mask);

#define C28X_CLRC_MODE(cpu_sr, mask) c28_gen_set_mode_flag(cpu_sr, mask, 0)
#define C28X_SETC_MODE(cpu_sr, mask) c28_gen_set_mode_flag(cpu_sr, mask, 1)

#endif