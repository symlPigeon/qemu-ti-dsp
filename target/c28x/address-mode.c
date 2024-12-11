#include "address-mode.h"
#include "cpu.h"

#define MASK_IMM6 0b111111
#define MASK_IMM3 0b111

static inline void gen_add(C28xLocDesc* desc) {
    tcg_gen_addi_tl(desc->ref_reg, desc->ref_reg, desc->width == C28X_LOC_16 ? 1 : 2);
}
static inline void gen_sub(C28xLocDesc* desc) {
    tcg_gen_subi_tl(desc->ref_reg, desc->ref_reg, desc->width == C28X_LOC_16 ? 1 : 2);
}
static inline void gen_set_arp(C28xLocDesc* desc) {
    uint32_t arp = desc->loc & MASK_IMM3;
    tcg_gen_movi_tl(desc->cpu_r[ARP_FLAG], arp);
}
static inline void gen_circular_indirect_access_hook(C28xLocDesc* desc) {
    TCGLabel* else_label = gen_new_label();
    TCGLabel* end_label = gen_new_label();
    TCGv xar6_lb = tcg_temp_new_i32();
    TCGv_i32 xar1_lb = tcg_temp_new_i32();
    tcg_gen_andi_tl(xar6_lb, desc->cpu_r[C28X_REG_XAR6], 0xFF);
    tcg_gen_andi_tl(xar1_lb, desc->cpu_r[C28X_REG_XAR1], 0xFF);
    tcg_gen_brcond_tl(TCG_COND_NE, xar6_lb, xar1_lb, else_label);
    // if XAR6(7:0) == XAR1(7:0)
    tcg_gen_andi_tl(desc->cpu_r[C28X_REG_XAR6], desc->cpu_r[C28X_REG_XAR6], 0xFFFFFF00);
    tcg_gen_br(end_label);
    gen_set_label(else_label);
    // else
    if (desc->width == C28X_LOC_16) {
        tcg_gen_addi_tl(desc->cpu_r[C28X_REG_XAR6], desc->cpu_r[C28X_REG_XAR6], 1);
    } else {
        tcg_gen_addi_tl(desc->cpu_r[C28X_REG_XAR6], desc->cpu_r[C28X_REG_XAR6], 2);
    }
    gen_set_label(end_label);
    // ARP = 6
    tcg_gen_movi_tl(desc->cpu_r[ARP_FLAG], 6);
    tcg_temp_free_i32(xar6_lb);
    tcg_temp_free_i32(xar1_lb);
}

#define _C28X_ARP_ACCESS_HOOK_FUNC(name, stmt)                                                                         \
    static inline void name(C28xLocDesc* desc) {                                                                       \
        TCGLabel* labels[9];                                                                                           \
        for (int i = 0; i < 9; i++) {                                                                                  \
            labels[i] = gen_new_label();                                                                               \
        }                                                                                                              \
        for (int i = 0; i < 8; i++) {                                                                                  \
            gen_set_label(labels[i]);                                                                                  \
            tcg_gen_brcondi_i32(TCG_COND_NE, desc->ref_reg, i, labels[i + 1]);                                         \
            stmt;                                                                                                      \
            tcg_gen_br(labels[8]);                                                                                     \
        }                                                                                                              \
        gen_set_label(labels[8]);                                                                                      \
    }

_C28X_ARP_ACCESS_HOOK_FUNC(gen_arp_add, tcg_gen_addi_tl(desc->cpu_r[C28X_REG_XAR0 + i], desc->cpu_r[C28X_REG_XAR0 + i],
                                                        desc->width == C28X_LOC_16 ? 1 : 2))
_C28X_ARP_ACCESS_HOOK_FUNC(gen_arp_sub, tcg_gen_subi_tl(desc->cpu_r[C28X_REG_XAR0 + i], desc->cpu_r[C28X_REG_XAR0 + i],
                                                        desc->width == C28X_LOC_16 ? 1 : 2))
_C28X_ARP_ACCESS_HOOK_FUNC(gen_arp_add_ar0, {
    TCGv tmp = tcg_temp_new_i32();
    tcg_gen_andi_tl(tmp, desc->cpu_r[C28X_REG_XAR0], 0xFFFF);
    tcg_gen_add_tl(desc->cpu_r[C28X_REG_XAR0 + i], desc->cpu_r[C28X_REG_XAR0 + i], tmp);
    tcg_temp_free_i32(tmp);
})
_C28X_ARP_ACCESS_HOOK_FUNC(gen_arp_sub_ar0, {
    TCGv tmp = tcg_temp_new_i32();
    tcg_gen_andi_tl(tmp, desc->cpu_r[C28X_REG_XAR0], 0xFFFF);
    tcg_gen_sub_tl(desc->cpu_r[C28X_REG_XAR0 + i], desc->cpu_r[C28X_REG_XAR0 + i], tmp);
    tcg_temp_free_i32(tmp);
})

void c28x_resolve_loc_desc(C28xLocDesc* desc, TCGv_i32 cpu_r[], TCGv_i32 cpu_sr[], uint8_t loc, uint8_t rw,
                           uint8_t width) {
    // we only implement C28x Mode, which means amode - 0
    desc->width = width;
    desc->rw = rw;
    desc->pre_hook = NULL;
    desc->post_hook = NULL;
    desc->cpu_r = cpu_r;
    desc->loc = loc;
    int flag = 0;

    if ((loc & 0b11000000) == 0) {
        // 0 0 III III : Direct Addressing Modes (DP)
        // 32bitDataAddr(31:22) = 0
        // 32bitDataAddr(21:6) = DP(15:0)
        // 32bitDataAddr(5:0) = 6bit
        desc->mode = C28X_MEM_DIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_DP];
        desc->offset = tcg_constant_i32(loc & MASK_IMM6);
        flag = 1;
    }
    if ((loc & 0b11000000) == 0b01000000) {
        // 0 1 III III : Stack Addressing Mode (SP)  *-SP[6bit]
        // 32bitDataAddr(31:16) = 0x0000
        // 32bitDataAddr(15:0) = SP - 6bit
        desc->mode = C28X_MEM_STACK_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_SP];
        desc->offset = tcg_constant_i32(-(loc & MASK_IMM6));
        flag = 1;
    }
    if (loc == 0b10111101) {
        // 1 0 111 101 : Stack Addressing Mode (SP)  *SP++
        // 32bitDataAddr(31:16) = 0x0000
        // 32bitDataAddr(15:0) = SP
        // if loc16 then SP++, else SP += 2
        desc->mode = C28X_MEM_STACK_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_SP];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_add;
        flag = 1;
    }
    if (loc == 0b10111110) {
        // 1 0 111 110 : Stack Addressing Mode (SP)  *--SP
        // if loc16 then SP--, else SP -= 2
        // 32bitDataAddr(31:16) = 0x0000
        // 32bitDataAddr(15:0) = SP
        desc->mode = C28X_MEM_STACK_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_SP];
        desc->offset = tcg_constant_i32(0);
        desc->pre_hook = gen_sub;
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10000000) {
        // 1 0 000 AAA : Indirect Addressing Mode  *XARn++
        // ARP = n
        // 32bitDataAddr(31:0) = XARn
        // if loc16 then XARn++, else XARn += 2
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_add;
        tcg_gen_movi_i32(cpu_r[ARP_FLAG], loc & MASK_IMM3);    // ARP = n
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10001000) {
        // 1 0 001 AAA : Indirect Addressing Mode  *--XARn
        // ARP = n
        // if loc16 then XARn--, else XARn -= 2
        // 32bitDataAddr(31:0) = XARn
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = tcg_constant_i32(0);
        desc->pre_hook = gen_sub;
        tcg_gen_movi_i32(cpu_r[ARP_FLAG], loc & MASK_IMM3);    // ARP = n
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10010000) {
        // 1 0 010 AAA : Indirect Addressing Mode  *+XARn[AR0]
        // ARP = n
        // 32bitDataAddr(31:0) = XARn + AR0
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = cpu_r[C28X_REG_XAR0];                   // note that only lower 16 bits are used
        tcg_gen_movi_i32(cpu_r[ARP_FLAG], loc & MASK_IMM3);    // ARP = n
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10011000) {
        // 1 0 011 AAA : Indirect Addressing Mode  *+XARn[AR1]
        // ARP = n
        // 32bitDataAddr(31:0) = XARn + AR1
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = cpu_r[C28X_REG_XAR1];                   // note that only lower 16 bits are used
        tcg_gen_movi_i32(cpu_r[ARP_FLAG], loc & MASK_IMM3);    // ARP = n
        flag = 1;
    }
    if ((loc & 0b11000000) == 0b11000000) {
        // 1 1 III AAA : Indirect Addressing Mode  *+XARn[3bit]
        // ARP = n
        // 32bitDataAddr(31:0) = XARn + 3bit
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = tcg_constant_i32((loc >> 3) & MASK_IMM3);    // imm value is treated as unsigned 3bit
        tcg_gen_movi_i32(cpu_r[ARP_FLAG], loc & MASK_IMM3);         // ARP = n
        flag = 1;
    }
    if (loc == 0b10111000) {
        // 1 0 111 000 : C2xLP Indirect Addressing Mode  *
        // 32bitDataAddr(31:0) = XAR(ARP)
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10111001) {
        // 1 0 111 001 : C2xLP Indirect Addressing Mode  *++
        // 32bitDataAddr(31:0) = XAR(ARP)
        // if loc16 then XAR(ARP)++, else XAR(ARP) += 2
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_arp_add;
        flag = 1;
    }
    if (loc == 0b10111010) {
        // 1 0 111 010 : C2xLP Indirect Addressing Mode  *--
        // 32bitDataAddr(31:0) = XAR(ARP)
        // if loc16 then XAR(ARP)--, else XAR(ARP) -= 2
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        desc->pre_hook = gen_arp_sub;
        flag = 1;
    }
    if (loc == 0b10111011) {
        // 1 0 111 011 : C2xLP Indirect Addressing Mode  *0++
        // 32bitDataAddr(31:0) = XAR(ARP)
        // XAR(ARP) = XAR(ARP) + AR0
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_arp_add_ar0;
        flag = 1;
    }
    if (loc == 0b10111100) {
        // 1 0 111 100 : C2xLP Indirect Addressing Mode  *0--
        // 32bitDataAddr(31:0) = XAR(ARP)
        // XAR(ARP) = XAR(ARP) - AR0
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        desc->pre_hook = gen_arp_sub_ar0;
        flag = 1;
    }
    if (loc == 0b10101111) {
        // 1 0 101 110 : C2xLP Indirect Addressing Mode  *BR0++
        // 32bitDataAddr(31:0) = XAR(ARP)
        // XAR(ARP)(15:0) = AR(ARP) rcadd AR0  **reverse carry added**
        // XAR(ARP)(31:16) = unchanged
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        // FIXME: i dont know how to write this QAQ
        printf("[C28X-TCG]: ERROR! loc16/loc32 unimplemented: *BAR0++\n");
        flag = 1;
    }
    if (loc == 0b10101111) {
        // 1 0 101 111 : C2xLP Indirect Addressing Mode  *BR0--
        // 32bitDataAddr(31:0) = XAR(ARP)
        // XAR(ARP)(15:0) = AR(ARP) rbsub AR0  **reverse carry sub**
        // XAR(ARP)(31:16) = unchanged
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        // FIXME: i dont know how to write this QAQ
        printf("[C28X-TCG]: ERROR! loc16/loc32 unimplemented: *BAR0--\n");
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10110000) {
        // 1 0 110 RRR : C2xLP Indirect Addressing Mode  *,ARPn
        desc->mode = C28X_MEM_INDIRECT_ACCESS_ARP_MODE;
        desc->ref_reg = cpu_sr[ARP_FLAG];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_set_arp;
        flag = 1;
    }
    if (loc == 0b10111111) {
        // 1 0 111 111 : Circular Indirect Addressing Modes  *AR6%++
        // 32bitDataAddr(31:0) = XAR6
        // if XAR6(7:0) == XAR1(7:0)
        //     XAR6(7:0) = 0x00
        //     XAR6(15:8) = unchanged
        // else
        //     if (16bit)
        //         XAR6(15:0) += 1
        //     else
        //         XAR6(15:0) += 2
        // XAR6(31:16) = unchanged
        // ARP = 6
        desc->mode = C28X_MEM_INDIRECT_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR6];
        desc->offset = tcg_constant_i32(0);
        desc->post_hook = gen_circular_indirect_access_hook;
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10100000) {
        // ? This conflicts with 16-bit Register Addressing Mode *ARn, WTF???
        // 1 0 100 AAA : 32-bit Register Addressing Mode @XARn
        // access 32 bit XARn
        desc->mode = C28X_MEM_REGISTER_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101001) {
        // 1 0 101 001 : 32-bit Register Addressing Mode ACC
        // access 32 bit ACC
        desc->mode = C28X_MEM_REGISTER_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_ACC];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
        // NOTE THAT THIS MAY AFFECT Z/N/V/C/OVC
    }
    if (loc == 0b10101011) {
        // 1 0 101 011 : 32-bit Register Addressing Mode P
        // access 32 bit P
        desc->mode = C28X_MEM_REGISTER_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_P];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101100) {
        // 1 0 101 100 : 32-bit Register Addressing Mode XT
        // access 32 bit XT
        desc->mode = C28X_MEM_REGISTER_ACCESS_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XT];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if ((loc & 0b11111000) == 0b10100000) {
        // 1 0 100 AAA : 16-bit Register Addressing Mode *ARn
        // access 16 bit ARn
        desc->mode = C28X_MEM_REGISTER_ACCESS_L_MODE;
        desc->ref_reg = cpu_r[C28X_REG_XAR0 + (loc & MASK_IMM3)];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101000) {
        // 1 0 101 000 : 16-bit Register Addressing Mode @AH
        // access 16 bit AH
        desc->mode = C28X_MEM_REGISTER_ACCESS_H_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_ACC];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101001) {
        // 1 0 101 001 : 16-bit Register Addressing Mode @AL
        // access 16 bit AL
        desc->mode = C28X_MEM_REGISTER_ACCESS_L_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_ACC];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101010) {
        // 1 0 101 010 : 16-bit Register Addressing Mode @PH
        // access 16 bit PH
        desc->mode = C28X_MEM_REGISTER_ACCESS_H_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_P];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101011) {
        // 1 0 101 011 : 16-bit Register Addressing Mode @PL
        // access 16 bit PL
        desc->mode = C28X_MEM_REGISTER_ACCESS_L_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_P];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101100) {
        // 1 0 101 100 : 16-bit Register Addressing Mode @TH
        // access 16 bit TH
        desc->mode = C28X_MEM_REGISTER_ACCESS_H_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_XT];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }
    if (loc == 0b10101101) {
        // 1 0 101 101 : 16-bit Register Addressing Mode @SP
        // access 16 bit SP
        desc->mode = C28X_MEM_REGISTER_ACCESS_L_MODE;
        desc->ref_reg = cpu_sr[C28X_REG_SP];
        desc->offset = tcg_constant_i32(0);
        flag = 1;
    }

    if (!flag) {
        printf("[C28X-TCG]: ERROR! loc16/loc32 unimplemented: %d\n", loc);
    }
}

#define _GENERATE_RW_MEM_CODE                                                                                          \
    tcg_gen_muli_tl(addr, addr, 2);                                                                                    \
    if (desc->rw == C28X_MEM_ACCESS_READ) {                                                                            \
        tcg_gen_qemu_ld_tl(reg, addr, 0, desc->width == C28X_LOC_16 ? MO_16 : MO_32);                                  \
    } else {                                                                                                           \
        tcg_gen_qemu_st_tl(reg, addr, 0, desc->width == C28X_LOC_16 ? MO_16 : MO_32);                                  \
    }

inline static void gen_c28x_loc_rw_direct_access_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv addr = tcg_constant_i32(0);
    tcg_gen_shli_tl(addr, desc->ref_reg, 6);
    tcg_gen_add_tl(addr, addr, desc->offset);

    _GENERATE_RW_MEM_CODE

    tcg_temp_free_i32(addr);
}

inline static void gen_c28x_loc_rw_stack_access_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv addr = tcg_constant_i32(0);
    tcg_gen_add_tl(addr, desc->ref_reg, desc->offset);
    tcg_gen_andi_tl(addr, addr, 0xFFFF);

    _GENERATE_RW_MEM_CODE

    tcg_temp_free_i32(addr);
}

inline static void gen_c28x_loc_rw_indirect_access_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv addr = tcg_temp_new_i32();
    TCGv addr_offset = tcg_temp_new_i32();

    tcg_gen_mov_tl(addr, desc->ref_reg);
    tcg_gen_andi_tl(addr_offset, desc->offset, 0xFFFF);
    tcg_gen_add_tl(addr, addr, addr_offset);

    _GENERATE_RW_MEM_CODE

    tcg_temp_free_i32(addr);
}

inline static void gen_c28x_loc_rw_indirect_arp_access_mode(C28xLocDesc* desc, TCGv reg) {
    TCGLabel* labels[9];
    for (int i = 0; i < 9; i++) {
        labels[i] = gen_new_label();
    }

    TCGv addr = tcg_temp_new_i32();    // offset should be 0
    for (int i = 0; i < 8; i++) {
        gen_set_label(labels[i]);
        tcg_gen_brcondi_tl(TCG_COND_NE, desc->ref_reg, i, labels[i + 1]);
        tcg_gen_mov_tl(addr, desc->cpu_r[C28X_REG_XAR0 + i]);
        tcg_gen_br(labels[8]);
    }
    gen_set_label(labels[8]);

    _GENERATE_RW_MEM_CODE

    tcg_temp_free_i32(addr);
}

inline static void gen_c28x_mem_register_access_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv target_reg = tcg_constant_i32(0);
    tcg_gen_mov_tl(target_reg, desc->ref_reg);

    if (desc->rw == C28X_MEM_ACCESS_READ) {
        tcg_gen_mov_tl(reg, target_reg);
    } else {
        tcg_gen_mov_tl(target_reg, reg);
    }
}

inline static void gen_c28x_mem_register_access_h_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv target_reg = tcg_constant_i32(0);
    tcg_gen_mov_tl(target_reg, desc->ref_reg);
    // target is high 16-bits, so width is useless
    if (desc->rw == C28X_MEM_ACCESS_READ) {
        tcg_gen_shri_tl(reg, target_reg, 16);
    } else {
        TCGv tmp = tcg_temp_new_i32();
        tcg_gen_shli_tl(tmp, reg, 16);
        tcg_gen_andi_tl(target_reg, target_reg, 0xFFFF);
        tcg_gen_or_tl(target_reg, target_reg, tmp);
        tcg_temp_free_i32(tmp);
    }
}

inline static void gen_c28x_mem_register_access_l_mode(C28xLocDesc* desc, TCGv reg) {
    TCGv target_reg = tcg_constant_i32(0);
    tcg_gen_mov_tl(target_reg, desc->ref_reg);
    if (desc->rw == C28X_MEM_ACCESS_READ) {
        tcg_gen_andi_tl(reg, target_reg, 0xFFFF);
    } else {
        TCGv tmp = tcg_temp_new_i32();
        tcg_gen_andi_tl(tmp, reg, 0xFFFF);
        tcg_gen_andi_tl(target_reg, target_reg, 0xFFFF0000);
        tcg_gen_or_tl(target_reg, target_reg, tmp);
        tcg_temp_free_i32(tmp);
    }
}

void gen_c28x_loc_rw(C28xLocDesc* desc, TCGv_i32 reg) {
    switch (desc->mode) {
    case C28X_MEM_DIRECT_ACCESS_MODE:
        gen_c28x_loc_rw_direct_access_mode(desc, reg);
        break;
    case C28X_MEM_STACK_ACCESS_MODE:
        gen_c28x_loc_rw_stack_access_mode(desc, reg);
        break;
    case C28X_MEM_INDIRECT_ACCESS_MODE:
        gen_c28x_loc_rw_indirect_access_mode(desc, reg);
        break;
    case C28X_MEM_INDIRECT_ACCESS_ARP_MODE:
        gen_c28x_loc_rw_indirect_arp_access_mode(desc, reg);
        break;
    case C28X_MEM_REGISTER_ACCESS_MODE:
        gen_c28x_mem_register_access_mode(desc, reg);
        break;
    case C28X_MEM_REGISTER_ACCESS_H_MODE:
        gen_c28x_mem_register_access_h_mode(desc, reg);
        break;
    case C28X_MEM_REGISTER_ACCESS_L_MODE:
        gen_c28x_mem_register_access_l_mode(desc, reg);
        break;
    default:
        printf("[C28X-TCG]: ERROR! loc16/loc32 unimplemented: %d\n", desc->mode);
    }
}