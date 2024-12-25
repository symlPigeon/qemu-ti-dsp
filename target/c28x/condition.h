#ifndef C28X_CPU_CONDITION_H
#define C28X_CPU_CONDITION_H

#include "qemu/osdep.h"

#include "cpu.h"
#include "tcg/tcg-op.h"

/**
 * @brief Generates a test condition for the C28x target.
 *
 * This function evaluates a condition code and sets the result accordingly.
 *
 * @param cond The condition code to evaluate.
 * @param result The TCGv variable where the result will be stored.
 * @param cpu_sr An array of TCGv variables representing the CPU status registers.
 */
void c28x_gen_test_condition(uint8_t cond, TCGv result, TCGv cpu_sr[]);

/**
 * @brief Parses a condition code for the C28x target.
 *
 * This function takes an 8-bit condition code and returns a string
 * representation of the condition for the C28x target.
 *
 * @param cond The 4-bit condition code to be parsed.
 * @return A constant character pointer to the string representation of the condition.
 */
const char* c28x_parse_condition(uint8_t cond);

#endif