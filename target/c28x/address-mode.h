#ifndef C28X_CPU_ADDRESS_MODE_H
#define C28X_CPU_ADDRESS_MODE_H

#include "qemu/osdep.h"

#include "cpu.h"
#include "tcg/tcg-op-common.h"
#include "tcg/tcg-op.h"
#include "tcg/tcg.h"

#define C28X_MEM_ACCESS_READ  0
#define C28X_MEM_ACCESS_WRITE 1

#define C28X_LOC_16 16
#define C28X_LOC_32 32

#define C28X_MEM_DIRECT_ACCESS_MODE       0
#define C28X_MEM_STACK_ACCESS_MODE        1
#define C28X_MEM_INDIRECT_ACCESS_MODE     2
#define C28X_MEM_INDIRECT_ACCESS_ARP_MODE 3
#define C28X_MEM_REGISTER_ACCESS_MODE     4
#define C28X_MEM_REGISTER_ACCESS_H_MODE   5
#define C28X_MEM_REGISTER_ACCESS_L_MODE   6

typedef struct C28xLocDesc {
    uint8_t mode;     // C28X_MEM_<MODE>_ACCESS_MODE
    uint8_t rw;       // READ or WRITE
    uint8_t width;    // the width of the data
    TCGv ref_reg;     // reference register, works as base address
                      // however, in ARP_MODE, it is the ARP register

    TCGv offset;    // offset value
                    // finally we access the memory by ref_reg + offset
                    // but in ARP_MODE, we access the memory by XAR(ref_reg)

    TCGv* cpu_r;    // store cpu_r here for convenience, just for ARP_MODE
    uint8_t loc;    // the loc address

    void (*pre_hook)(struct C28xLocDesc* desc);     // hook before the memory access
    void (*post_hook)(struct C28xLocDesc* desc);    // hook after the memory access
} C28xLocDesc;

// We hope that C2xLP will not be used anymore
// As this will cause A LOT OF TROUBLE
void c28x_resolve_loc_desc(C28xLocDesc* desc, TCGv cpu_r[], TCGv cpu_sr[], uint8_t loc, uint8_t rw, uint8_t width);
void c28x_gen_loc_rw(C28xLocDesc* desc, TCGv_i32 reg);
char* c28x_parse_loc_desc(uint8_t loc);

// So an ordinary read operation will be like this
// C28X_READ_LOC16(loc, reg)
//  1. malloc a C28xLocDesc
//  2. resolve the loc address
//  3. call pre_hook if exists
//  4. read the memory to reg
//  5. call post_hook if exists
//  6. free the C28xLocDesc
//
// However, an ordinary write operation will be much more complex
// 1. C28X_READ_LOC16(loc, reg)   <===== READ
//   1.1 malloc a C28xLocDesc
//   1.2 resolve the loc address
//   1.3 call pre_hook if exists
//   1.4 read the memory to reg
//      <------ DO NOT CALL THE post_hook! -->
//   1.5 free the C28xLocDesc
// 2. DO SOMETHING TO reg         <===== MODIFY
//
// 3. C28X_WRITE_LOC16(loc, reg)  <===== WRITE
//   3.1 malloc a C28xLocDesc
//   3.2 resolve the loc address
//      <------ DO NOT CALL THE pre_hook! -->
//   3.3 write the memory from reg
//   3.4 call post_hook if exists
//   3.5 free the C28xLocDesc
//
// To distinguish the read and write operation, we use the `rmw` parameter
// Read-Modify-Write
// some loc address will be modified before/after the memory access, like *SP++ and *--SP
// when we perform a R-M-W operation, the address should not be modified before writing back
// so we have to disable the post_hook of read & pre_hook of write

#define C28X_RESOLVE_LOC(loc, reg, cpu_r, cpu_sr, _rw, width, rmw)                                                     \
    {                                                                                                                  \
        C28xLocDesc* desc = g_malloc(sizeof(C28xLocDesc));                                                             \
        c28x_resolve_loc_desc(desc, cpu_r, cpu_sr, loc, _rw, width);                                                   \
        if (desc->pre_hook && !(rmw && desc->rw)) desc->pre_hook(desc);                                                \
        c28x_gen_loc_rw(desc, reg);                                                                                    \
        if (desc->post_hook && (!rmw || desc->rw)) desc->post_hook(desc);                                              \
        g_free(desc);                                                                                                  \
    }

#endif