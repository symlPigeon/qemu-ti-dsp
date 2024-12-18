#ifndef C28X_CPU_CONDITION_H
#define C28X_CPU_CONDITION_H

#include "qemu/osdep.h"

#include "cpu.h"
#include "tcg/tcg-op.h"

void c28x_gen_test_condition(uint8_t cond, TCGv result, TCGv cpu_sr[]);
const char* c28x_parse_condition(uint8_t cond);

#endif