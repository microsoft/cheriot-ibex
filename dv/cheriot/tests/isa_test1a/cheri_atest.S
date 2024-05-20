#.option norelax

.section .text
#.globl cheri_fault_handler
.globl cheri_atest

.macro PRINTMSG reg, symbol
    lui        \reg, %hi(\symbol)
    addi       \reg, \reg, %lo(\symbol)
    csetaddr   c9, c6, \reg
    ccall      print_string
.endm

print_string:                           # print a string pointed by C9
    cincoffset csp, csp, -8
    csc c11, (csp)

    clb x11, (c9)
print_loop:
    csb x11, 512(c5)
    cincoffset c9, c9, 0x1
    clb x11, (c9)
    bne x11, x0, print_loop

    clc c11, (csp)
    cincoffset csp, csp, 8
    cret

#
#  Register allocation for this test
#
#   Globals
#   --  c2: as the stack capability (created at startup)
#   --  c3: as a "full" memory capability (entire address space)  
#   --  c4: base capability for code execution from SRAM (code r/x)
#   --  c5: base capability for peripheral accesses in tb_top 
#   --  c6: base capability for accessing SRAM (data and cap r/w)
#   --  c7: reserved for further use 
#
#   --  x1/cra: return address  
#   --  x10/a0: argument/return value for subroutines
#   --  x15/a5: is used to pass "argument" to the fault handler.
#
#   --  x8, x9(s0,s1): temp variables
#   --  x11-x14 (a1-a4): temp varaibles


#  ///////////////////////////////////////
#  --- CHERI fault hander 
#      - called by the exception handler (startup)
#  ///////////////////////////////////////

.align 4   # riscv vectors must be 4-bytes aligned

cheri_fault_handler:
    # save context to stack QQQ
    cincoffset csp, csp, -24    # SP-16
    csc cra, (csp) 
    csc c13, 8(csp) 
    csc c14, 16(csp) 

    addi x14, x0, 0
    beq x15, x14, case0         # load/store fault (cheri error)
    addi x14, x0, 1
    beq x15, x14, case1         # jump fault
    addi x14, x0, 3
    beq x15, x14, case3         # misc fault
    addi x14, x0, 5
    beq x15, x14, case5         # pcc fault
    addi x14, x0, 6
    beq x15, x14, case6         # pcc fault
    addi x14, x0, 7
    beq x15, x14, case7         # pcc fault
    addi x14, x0, 8 
    beq x15, x14, case8         # pcc fault

    j echo1

case0:   
    # cmove c12, c8             # not used
    j echo1

case1:
    #csetaddr c8, c4, x11       # not used
    j echo1

case3:
    #cspecialw mepcc, c8        # not used
    j echo1

case5:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1    

case6:
    cspecialr c13, mepcc
    cspecialw mscratchc, c13
    li x15, 7                 # move on the case 7 to recover from the fault
    j echo1    

case7:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1 
   
case8:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1    

echo1:
    addi x13, x0, 0x66                
    csb x13, 512(c5)                
    addi x13, x0, 0x61                
    csb x13, 512(c5)                
    addi x13, x0, 0x75                
    csb x13, 512(c5)                
    addi x13, x0, 0x6c                
    csb x13, 512(c5)                
    addi x13, x0, 0x74                
    csb x13, 512(c5)                
    addi x13, x15, 0x30      
    csb x13, 512(c5)
    addi x13, x0,0x20                
    csb x13, 512(c5)                
    addi x13, x0,0x4f                
    csb x13, 512(c5)                
    addi x13, x0,0x4b                
    csb x13, 512(c5)
    addi x13, x0, 0xa                
    csb x13, 512(c5)                
    addi x13, x0,0xd                
    csb x13, 512(c5)                

exit_handler:
    clc cra, (csp) 
    clc c13, 8(csp) 
    clc c14, 16(csp) 
    cincoffset csp, csp, 24    # SP+16
    mret             


#  ///////////////////////////////////////
#  init
#  ///////////////////////////////////////

test_init:
    # setup fault handler for this test suite
    cspecialr ct0, mtcc
1:  auipcc  ct1, %cheri_compartment_pccrel_hi(cheri_fault_handler)
    cincoffset ct1, ct1, %cheri_compartment_pccrel_lo(1b)
    csetaddr ct0, ct0, t1
    cspecialw mtcc, ct0

    cspecialrw c3, mtdc, c0    # read MTDC address 'd29, memory root

    lui x11, 0x83800   
    csetaddr c5, c3, x11      # set base address to 0x8400_0000
    csetboundsimm c5, c5, 0x800   # set bounds to 0x800
    addi x11, x0, 0x24            
    candperm c5, c5, x11      # load/store data permission only 

    lui x11, 0x80000   
    csetaddr c6, c3, x11      # set base address to 0x8000_0000
    lui x11, 0x4000   
    csetbounds c6, c6, x11    # set lengths to 0x400_0000
    addi x11, x0, 0x7f    
    candperm c6, c6, x11      # full mem data/cap permission only
   
    auipcc c4, 0             # get PCC capability
    lui x11, 0x80000   
    csetaddr c4, c4, x11      # set address to 0x8000_0000
    lui x11, 0x40   
    csetbounds c4, c4, x11    # set length to 0x80000
   
    cspecialr c7, mscratchc   # sealing root

    li a0, 0x0
    cret

#  ///////////////////////////////////////
#  Test PCC fetch faults and mepcc, test 1
#  ///////////////////////////////////////

test_pccft1:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    # After the sail change of delayed bound checking (PR37)
    # case 1 and case 2 became similar (both clears tag of mepcc)

    # case 1: pcc fetch bound violation, 
    #         handler recovers mepcc (by writing a saved cap to it)  
    lui x11, %hi(pccft1_1)
    addi  x11, x11, %lo(pccft1_1)
    cmove c8, c4
    csetaddr c8, c8, x11
    csetboundsimm c9, c8, 8   
    li x15, 5             // call argument for fault handler
    cjalr c0, 0(c9)       // tighten PCC bounds

pccft1_1:     
    beq x0, x0, pccft1_1_ok   // this should cause a fetch error
    nop
    nop
    nop
    nop
    nop
    nop
    nop

pccft1_1_ok:
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, pccft1_fail
    csrr x13, mtval
    li x12, 0x401              
    bne x12, x13, pccft1_fail
    nop

    # case 2: pcc fetch violation 
    #         2 faults (first by fectch violation, 2nd by mret/illegal mepcc)
    #         handler does NOT recover mepcc on the 1st fault, thus mret causes 2 nd fault
    lui x11, %hi(pccft1_2)
    addi  x11, x11, %lo(pccft1_2)
    cmove c8, c4
    csetaddr c8, c8, x11
    csetboundsimm c9, c8, 8   

    lui x11, %hi(pccft1_2_ok)      // allow c8 to jump to pccft1_2_ok (recover)
    addi  x11, x11, %lo(pccft1_2_ok)
    cmove c8, c4
    csetaddr c8, c8, x11
    
    li x15, 6                     // call argument for fault handler
    cjalr c0, 0(c9)               // tighten PCC bounds

pccft1_2:
    beq x0, x0, -100               // somewhere far away enough? 0000 
    nop 
    nop
    nop

pccft1_2_ok:
    cspecialr c13, mscratchc      # check mepcc from case 6 (tag cleared)
    cgettag x11, c13
    bne x11, x0, pccft1_fail
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, pccft1_fail
    csrr x13, mtval              
    li x12, 0x402                 # tag violation (mepcc tag cleared)              
    bne x12, x13, pccft1_fail

    li a0, 0x0
    j pccft1_exit

pccft1_fail:
    li a0, 0xfa     # error code

pccft1_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  Test PCC fetch faults and mepcc, test 2 
#  ///////////////////////////////////////
test_pccft2:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    # case 1: pcc fetch violation, 
    # write an tag =  0 capability to mepc and use mret to jump to it (PCC)

    lui x11, %hi(pccft2_1)
    addi  x11, x11, %lo(pccft2_1)
    cmove c8, c4
    csetaddr c8, c8, x11      // save recovery address

    csetboundsimm c9, c8, 8   
    li x15, 8                 // call argument for fault handler

    cspecialw mepcc, c11

    li x12, 0x00001800        // bit 12:11 (MPP) = 3 to stay in M-priv level
    csrs mstatus, x12         
    mret                      // jump to the new PCC

pccft2_1:     
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, pccft2_fail
    csrr x13, mtval              
    li   x12, 0x402               # tag violation
    bne x12, x13, pccft2_fail
    nop

    # case 2: pcc fetch violation, 
    # Write a perm_ex = 0 capability to mepc and use mret to jump to it (PCC)

    lui x11, %hi(pccft2_2)
    addi  x11, x11, %lo(pccft2_2)
    cmove c8, c4
    csetaddr c8, c8, x11      // save recovery address

    csetboundsimm c9, c8, 8   
    li x15, 8                 // call argument for fault handler

    li x12, 0xfe00
    auipcc c11, 0
    candperm c11, c11, x12     // remove PERM_EX
    cspecialw mepcc, c11
    cspecialr c11, mepcc
    cgettag x11, c11
    bne x11, x0, pccft2_fail  // mepcc legalization should clear tag

    li x12, 0x00001800        // bit 12:11 (MPP) = 3 to stay in M-priv level
    csrs mstatus, x12         
    mret                      // jump to the new PCC

pccft2_2:     
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, pccft2_fail
    csrr x13, mtval              
    li   x12, 0x402               # tag violation
    bne x12, x13, pccft2_fail

    # case 3: pcc fetch violation, 
    # Write a sealed capability to mepc and use mret to jump to it (PCC)

    lui x11, %hi(pccft2_3)
    addi  x11, x11, %lo(pccft2_3)
    cmove c8, c4
    csetaddr c8, c8, x11      // save recovery address

    csetboundsimm c9, c8, 8   
    li x15, 8                 // call argument for fault handler

    cmove c12, c7             # sealing root
    addi x11, x0, 0x7
    csetaddr c12, c12, x11

    auipcc c11, 0
    cseal c11, c11, c12
    cspecialw mepcc, c11

    li x12, 0x00001800        // bit 12:11 (MPP) = 3 to stay in M-priv level
    csrs mstatus, x12         
    mret                      // jump to the new PCC

pccft2_3:     
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1
    #bne x12, x13, pccft2_fail

    li a0, 0x0
    j pccft2_exit

pccft2_fail:
    li a0, 0xfc     # error code

pccft2_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  Test stack high watermark feature
#  ///////////////////////////////////////
test_shwm:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)  

    cspecialrw c6, mtdc, c0       # read MTDC address 'd29, memory root
    li x11, 0x80010000
    csetaddr c8, c6, x11
    csw x11, 28(c8)               # initialize the address so that we won't get X complaints

    li x11, 0x80010000
    csrw 0xbc2, x11               # WM Base
    li x11, 0x80010020
    csrw 0xbc1, x11               # WM ptr
    csrr x12, 0xbc1               # verify we can write to the newCSR
    bne x12, x11, shwm_fail

    clw x11, 28(c8)               # verify read access won't change WM
    csrr x12, 0xbc1
    li x11, 0x80010020
    bne x12, x11, shwm_fail

    csw x11, 28(c8)               # verify update WM (round down)
    csrr x12, 0xbc1
    li x11, 0x80010010
    bne x12, x11, shwm_fail
    csw x11, 16(c8)
    csrr x12, 0xbc1
    li x11, 0x80010010
    bne x12, x11, shwm_fail

    csw x11, -16(c8)              # verify out-of-bound access won't change WM
    csrr x12, 0xbc1
    li x11, 0x80010010
    bne x12, x11, shwm_fail

    csw x11, 4(c8)                # verify round down to base
    csrr x12, 0xbc1
    li x11, 0x80010000
    bne x12, x11, shwm_fail

    csrr x12, 0xbc2
    li x11, 0x80010000
    bne x12, x11, shwm_fail
   
shwm_done:
    li a0, 0x0
    j shwm_exit

shwm_fail:
    li a0, 0xe0    # error code

shwm_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  Test MTCC/mepcc legalization
#  ///////////////////////////////////////
test_mtcc:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    # test mtvec legalization
    cspecialr c8, mtcc     # save mtcc
    cgettag x11, c8
    beq x11, x0, mtcc_fail

    cmove c9, c8
    li x11, 0x1eff
    candperm c9, c9, x11   # remove perm_ex
    cspecialw mtcc, c9
    cspecialr c9, mtcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    cmove c10, c7           # sealing root
    addi x11, x0, 0x5
    csetaddr c10, c10, x11
    cmove c9, c8
    cseal c9, c9, c10       # seal and write to mtcc
    cspecialw mtcc, c9
    cspecialr c9, mtcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    cmove c9, c8
    cincoffset c9, c9, 1    # addr[1:0] != 0;
    cspecialw mtcc, c9
    cspecialr c9, mtcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    cmove c9, c8
    cincoffset c9, c9, 2    # addr[1:0] != 0;
    cspecialw mtcc, c9
    cspecialr c9, mtcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    cmove c9, c8
    cincoffset c9, c9, 3    # addr[1:0] != 0;
    cspecialw mtcc, c9
    cspecialr c9, mtcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    cspecialw mtcc, c8     # restore mtcc
    cspecialr c9, mtcc     
    cseqx x11, c8, c9
    beq x11, x0, mtcc_fail

    # test address[0] of mepcc write
mepcc_test:
    auipcc c9, 0
    cspecialw mepcc, c9
    cspecialr c9, mepcc
    cgettag x11, c9
    beq x11, x0, mtcc_fail
     
    cincoffset c9, c9, 1    # addr[1:0] != 0;
    cspecialw mepcc, c9
    cspecialr c9, mepcc
    cgettag x11, c9
    bne x11, x0, mtcc_fail

    li a0, 0x0
    j mtcc_exit

mtcc_fail:
    li a0, 0xea     # error code

mtcc_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  Test CLC permission behaviors
#  ///////////////////////////////////////
test_clcp:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp) 

    li x11, 0x80010000
    csetaddr c8, c6, x11
    csc c6, 32(c8)

    li x11, 0x1fbf      # remove PERM_MC
    candperm c9, c8, x11

    # tag is cleared if auth_cap doesn't have PERM_MC
    clc c12, 32(c8)
    cseqx x11, c12, c6
    beq x11, x0, clcp_fail

    clc c13, 32(c9)
    ccleartag c12, c12
    cseqx x11, c12, c13
    beq x11, x0, clcp_fail

    # //if tag is already cleared, remove PERM_LG from cs1 does not change perms 
    clc c12, 32(c8)
    li x11, 0x1fbd       # remove PERM_MC and PERM_LG
    candperm c9, c8, x11
    clc c13, 32(c9)
    ccleartag c12, c12
    cseqx x11, c12, c13
    beq x11, x0, clcp_fail
    
    # //if tag is not cleared, remove PERM_LG from cs1 clears PERM_LG/PERM_GL on loaded cap 
    clc c12, 32(c8)
    li x11, 0x1ffd       # remove PERM_MC and PERM_LG
    candperm c9, c8, x11
    clc c13, 32(c9)
    li x11, 0x1ffc
    candperm c12, c12, x11
    cseqx x11, c12, c13
    beq x11, x0, clcp_fail

clcp_done:
    li a0, 0x0
    j clcp_exit

clcp_fail:
    li a0, 0xe0    # error code

clcp_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret


#  ///////////////////////////////////////
#  --- cheri_test (main test for CHERI instructions)
#  ///////////////////////////////////////

cheri_atest:
    # save register context so that we won't have issue talking with the C program 
    # note RISC-V uses x10/x11 (a0/a1) for args/return values, and x12-x17 (a2-7) for args
    cincoffset csp, csp, -64    
    csc c1, 0(csp)                
    csc c3, 8(csp)                
    csc c4, 16(csp)                
    csc c5, 24(csp)                
    csc c6, 32(csp)                
    csc c7, 40(csp)                
    csc c8, 48(csp)                
    csc c9, 56(csp)                

    ccall test_init
    PRINTMSG x11, hello_msg

    PRINTMSG x11, test_pccft1_msg
    ccall test_pccft1
    bne a0, x0, test_exit

    PRINTMSG x11, test_pccft2_msg
    ccall test_pccft2
    bne a0, x0, test_exit

    PRINTMSG x11, test_mtcc_msg
    ccall test_mtcc
    bne a0, x0, test_exit

    PRINTMSG x11, test_clcp_msg
    ccall test_clcp
    bne a0, x0, test_exit

    PRINTMSG x11, test_shwm_msg
    ccall test_shwm
    bne a0, x0, test_exit

test_exit:
    # restore register context
    clc c1, 0(csp)                
    clc c3, 8(csp)                
    clc c4, 16(csp)                
    clc c5, 24(csp)                
    clc c6, 32(csp)                
    clc c7, 40(csp)                
    clc c8, 48(csp)                
    clc c9, 56(csp)                
    cincoffset csp, csp, 64

    cret

.section .rodata

hello_msg :
  .string "Running assembly test suite\n"
test_pccft1_msg :
  .string "Testing PCC fetch fault, part 1.. \n"
test_pccft2_msg :
  .string "Testing PCC fetch fault, part 2.. \n"
test_shwm_msg :
  .string "Testing MSHWM.. \n"
test_mtcc_msg :
  .string "Testing SCR.. \n"
test_clcp_msg :
  .string "Testing CLC permissions.. \n"

#.section .tohost
#tohost :
#  .dword 0
#fromhost :
#  .dword 0
