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
#   --  c7: sealing root
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
    addi x14, x0, 2
    beq x15, x14, case2         # load/store fault (rv32 cheri error)
    addi x14, x0, 3
    beq x15, x14, case3         # SCR access fault
    addi x14, x0, 4
    beq x15, x14, case4         # CSR access fault
    addi x14, x0, 5
    beq x15, x14, case5         # CSR access fault

    j echo1

case0:   
    cmove c12, c8 
    j echo1

case1:
    cmove c8, c12 
    j echo1

case2:
    cmove c12, c8
    j echo1

case3:
case4:
case5:
    cspecialw mepcc, c8
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
    csetaddr c5, c3, x11      # set base address to 0x8380_0000
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
   
    cspecialr c7, mscratchc

    li a0, 0x0
    cret


#  ///////////////////////////////////////
#  ///////////////////////////////////////
#  test set_bounds
#  ///////////////////////////////////////
test_bounds:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    # test  set_bounds operations
    # first start with an unaligned address, so set_bounds should work but 
    # set_bounds_exact should fail
    li x11, 0x80010123   
    csetaddr c8, c6, x11 
    li x11, 0x800
    csetbounds c12, c8, x11
    csetboundsimm c13, c8, 0x800
    csetequalexact x14, c12, c13
    beq x14, x0, bounds_fail1
    cgettag x14, c12
    beq x14, x0, bounds_fail1
    cgetbase x14, c12

    csetboundsexact c12, c8, x11 
    cgettag x14, c12
    bne x14, x0, bounds_fail1

    # now align the address so that set_bounds_ext passes
    li x11, 0x80010128  
    csetaddr c8, c6, x11 
    li x11, 0x800
    csetboundsexact c12, c8, x11 
    cgettag x14, c12
    beq x14, x0, bounds_fail1

    # build caps with corner case top/base values (0x0 and 0x1ff)
    li x11, 0x800101ff     
    csetaddr c8, c6, x11 
    csetboundsimm c8, c8, 0x1     # top = 0x0, base = 0x1ff
    andi x11, x11, 0xff
    csb x11, (c8)
    clbu x12, (c8)
    bne x11, x12, bounds_fail2

    li x11, 0x80010000    
    csetaddr c8, c6, x11 
    li x11, 0x1ff0
    csetbounds c8, c8, x11        # top = 0x1ff, base = 0x0
    csw x11, 12(c8)
    clw x12, 12(c8)
    bne x11, x12, bounds_fail2

    # test crrl/cram, different length value
    li x11, 127
    crrl x12, x11
    cram x12, x11
    li x11, 4096
    crrl x12, x11
    cram x12, x11
    li x11, 8193
    crrl x12, x11
    cram x12, x11
    li x11, 65535
    crrl x12, x11
    cram x12, x11

    li a0, 0x0
    j bounds_exit

bounds_fail1:
    li a0, 0xf1     # error code
    j bounds_exit

bounds_fail2:
    li a0, 0xf2     # error code
    j bounds_exit

bounds_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  test set_addr, etc. corner cases 
#  ///////////////////////////////////////
test_addr:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)

    # test the exp=24 case (set_addr allows addr < base32)
    cspecialr c8, mtdc
    li x9, 0x74000010
    cincoffset c8, c8, x9
    csetbounds c8, c8, x9
    cincoffsetimm c8, c8, -0x7d1
    csetbounds c8, c8, x9
    cgettag x11, c8
    bne x11, x0, addr_fail

    # test rollowver case of incaddr
    li x12, 1024
    cmove c8, c5       // length = 800, offset = 0;
    cincoffsetimm c8, c8, 0x400 
    cmove c9, c8

test_addr1:
    cincoffsetimm c8, c8, 4
    cincoffsetimm c9, c9, -4
    addi x12, x12, -1
    bne x12, x0, test_addr1

    li a0, 0x0
    j addr_exit

addr_fail:
    li a0, 0xb1     # error code
    j bounds_exit

addr_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  test seal/unseal 
#  ///////////////////////////////////////
test_seal:
    cincoffset csp, csp, -64    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                
    csc c1,  48(csp)                

    # seal/unseal, interrupt enable/disable with sentries
    cmove  c8, c7           # sealing root
    addi x11, x0, 14
    csetaddr c8, c8, x11
  
    # seal+unseal should get the original cap back
    cseal c11, c6, c8
    cunseal c11, c11, c8
    csetequalexact x9, c11, c6
    beq x9, x0, seal_fail

    # jump to sentries with interrupt disabled
    li x11, 0x2                        # sentry = disable intr
    csetaddr  c8, c8, x11 
2: 
    auipcc  c9, %cheri_compartment_pccrel_hi(seal_cont1)
    cincoffset c9, c9, %cheri_compartment_pccrel_lo(2b)
    cseal c9, c9, c8                   # seal with
    cjalr c1, 0(c9)
    cjal seal_cont2

seal_cont1:
    nop
    nop
    csrr x11, mstatus                 # find mie status
    andi x11, x11, 0x08
    bne x11, x0, seal_fail
    
    # jump to sentries with interrupt enabled
    cjalr c0, 0(c1)

seal_cont2:
    nop
    nop
    csrr x11, mstatus
    andi x11, x11, 0x08
    beq x11, x0, seal_fail

    li a0, 0x0
    j seal_exit
seal_fail:
    li a0, 0xf2     # error code

seal_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    clc c1,  48(csp)                
    cincoffset csp, csp, 64    
    cret

#  ///////////////////////////////////////
#  test revocation
#  ///////////////////////////////////////
test_tsafe:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    lui x11, 0x80010   
    csetaddr c8, c6, x11          # set address to 0x8001_0000
    
    # build a new capability in c11  
    lui x11, 0x80001  
    csetaddr c11, c6, x11      
    csetboundsimm c11, c11, 0x800    # set lengths to 0x800, base/address to 0x8000_1000

    # store + load, unrevoked
    csc c11, 32(c8)
    clc c9, 32(c8)
    csetequalexact x12, c9, c11
    beq x12, x0, tsafe_fail

    # revoke the memory pointed by c11
    lui x12, 0x83000
    csetaddr c13, c6, x12       # set address to 0x8300_0000 (revocation map base)
    li x12, 1
    csw x12, 64(c13)            # set revocation map bit

    clc c9, 32(c8)
    cgettag x12, c9
    bne x12, x0, tsafe_fail   # returned cap.tag should be cleared
    cincoffset c9, c9, 0      # verify ECC updated correctly

    # test the WAR corner case, make sure CLC/tag clearing doesn't affect the write
    clc c9, 32(c8)
    cmove c9, c8              # this should stall till CLC/trvk is done
    csetequalexact x12, c9, c8
    beq x12, x0, tsafe_fail

    li x11, 0x12345678
    clc c9, 32(c8)
    add x9, x0, x11           # this should not stall but tag doesn't matter
    bne x11, x9, tsafe_fail

    li a0, 0x0
    j tsafe_exit

tsafe_fail:
    li a0, 0xf4     # error code

tsafe_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  test jump faults
#  ///////////////////////////////////////

test_jump:
    cincoffset csp, csp, -64    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                
    csc c1,  48(csp)                

    # enable ts_safe and do load cap again
    # JAL test case

    li x13, 0x246
    add x12, x0, x0
    cjal c1, test_jal1
    beq x12, x13, test_jalr
    j jump_fail

test_jal1:
    addi x12, x12, 0x123
    addi x12, x12, 0x123
    cjr c1

    # JALR test case 1, tag+perm_ex violation
test_jalr:
    lui x11, %hi(jalr_ok1)         # "correct" jump target
    addi  x11, x11, %lo(jalr_ok1)
    addi  x11, x11, -4             # artificially introduce an offset to test JALR
    csetaddr c12, c4, x11

    cincoffset c8, c5, 1024        # just some code here to check cincoffset with sail,
    cincoffset c8, c8, 1028        
    ccleartag c8, c8 
    addi x15, x0, 1                # use x15 to pass argument to fault handler
    cjalr c9, 4(c8)                # go to fault for the 1st time,  handler will fix c8 and resume

jalr_ok1:
    csrr x13, mcause              # check mcause and mtval
    li   x11, 0x1c
    bne x11, x13, jump_fail
    csrr x13, mtval
    li   x11, 0x0102               # cause = tag violation
    bne x11, x13, jump_fail

    # JALR test case 2, perm_ex violation only
    lui x11, %hi(jalr_ok2)          # "correct" jump target
    addi  x11, x11, %lo(jalr_ok2)
    addi  x11, x11, -16             # artificially introduce an offset to test JALR
    csetaddr c12, c4, x11

    lui x11, %hi(jump_fail)          # "failure" jump target
    addi  x11, x11, %lo(jump_fail)
    addi  x11, x11, -16             
    csetaddr c8, c4, x11
    li x11, 0x1eff
    candperm c8, c8, x11             # clear EX permission 
    addi x15, x0, 1                
    cjalr c9, 16(c8)                

jalr_ok2:
    csrr x13, mcause              # check mcause and mtval
    li   x11, 0x1c
    bne x11, x13, jump_fail
    csrr x13, mtval
    li   x11, 0x0111
    bne x11, x13, jump_fail

    # JALR test case 3, sealed jump target
    lui x11, %hi(jalr_ok3)          # "correct" jump target
    addi  x11, x11, %lo(jalr_ok3)
    addi  x11, x11, -24             # artificially introduce an offset to test JALR
    csetaddr c12, c4, x11

    lui x11, %hi(jump_fail)          # "failure" jump target
    addi  x11, x11, %lo(jump_fail)
    addi  x11, x11, -16             
    csetaddr c8, c4, x11

    cmove  c9, c7                    # sealing root
    addi x11, x0, 7
    csetaddr c9, c9, x11
    cseal c8, c8, c9                 # seal jump target
 
    addi x15, x0, 1                
    cjalr c9, 24(c8)                

jalr_ok3:
    csrr x13, mcause              # check mcause and mtval
    li   x11, 0x1c
    bne x11, x13, jump_fail
    csrr x13, mtval
    li   x11, 0x0103
    bne x11, x13, jump_fail

    # verify unaligned offset doesn't cause exceptions
    lui x11, %hi(jalr_ok4)          
    addi  x11, x11, %lo(jalr_ok4)
    csetaddr c8, c8, x11
    j jalr_ok4
.align 4   
jalr_ok4:
    cjalr c0, 5(c8)  # offset rounded down to 4, no exceptions, just move to next instr
    nop
    nop
    nop
    nop

    li a0, 0x0
    j jump_exit

jump_fail:
    li a0, 0xf5     # error code

jump_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    clc c1,  48(csp)                
    cincoffset csp, csp, 64   
    cret


#  ///////////////////////////////////////
#  test load/store fault conditions
#  ///////////////////////////////////////

test_lsft:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)


    # test clc/csc with cheri fault
    lui x11, 0x80010   
    csetaddr c8, c6, x11          # set address to 08001_0000

    addi x15, x0, 0               # pass argument to fault handler
    li  x12, 0x80010011           # clear tag, misaligned address
    csetaddr c12, c5, x12         
    csc c5, (c12)                 # introduce a store fault

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x13, x12, lsft_fail1
    csrr x13, mtval
    li   x12, 0x182
    bne x13, x12, lsft_fail1

lsft_case1:
    li  x12, 0x80010011           # clear tag, misaligned address
    csetaddr c12, c5, x12         
    clc c11, (c12)                # introduce a load fault

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x13, x12, lsft_fail1
    csrr x13, mtval
    li   x12, 0x182
    bne x13, x12, lsft_fail1

    li  x12, 0x80010011           # misaligned address only
    csetaddr c12, c6, x12         
    clc c11, (c12)                # introduce a load fault
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x4
    bne x13, x12, lsft_fail1
    csrr x13, mtval
    li   x12, 0x80010011
    bne x13, x12, lsft_fail1

lsft_case2:
    li  x12, 0x80010000           # address bound vio, misaligned address
    csetaddr c12, c6, x12
    csetboundsimm c12, c12, 0x20
    cincoffsetimm c12, c12, 29         
    clc c11, (c12)              # introduce a load fault

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne  x13, x12, lsft_fail2
    csrr x13, mtval
    li   x12, 0x181
    bne  x13, x12, lsft_fail2

# test rv32 access cheri faults
lsft_case3:
    li x11, 0x80010013            # unaligned access   
    csetaddr c8, c6, x11          # set address to 08001_0000
    addi x15, x0, 2               # pass argument to fault handler

    li  x11, 0xfffffffc           # address bound vio, top oaddress space
    csetaddr c12, c3, x11
    csetboundsimm c12, c12, 4
    li  x11, 0xffffffff
    csetaddr c12, c12, x11
    li  x11, 0xdeadbeef
    csw x11, (c12)                # introduce a store fault

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne  x13, x12, lsft_fail3
    csrr x13, mtval
    li   x12, 0x181
    bne  x13, x12, lsft_fail3

    li a0, 0x0
    j lsft_exit

lsft_fail1:
    li a0, 0xf6     # error code
    j lsft_exit

lsft_fail2:
    li a0, 0xf7     # error code
    j lsft_exit

lsft_fail3:
    li a0, 0xf7     # error code
    j lsft_exit


lsft_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret


#  ///////////////////////////////////////
#  test scr accesses 
#  ///////////////////////////////////////

test_scr:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    #
    # test SCR access wo/ ASR permission
    # 
    cspecialr c11, mtcc             # save content
5: 
    auipcc  c8, %cheri_compartment_pccrel_hi(scr_cont2)    # save original pcc/pc in C8
    cincoffset c8, c8, %cheri_compartment_pccrel_lo(5b)
6:
    auipcc  c9, %cheri_compartment_pccrel_hi(scr_cont1)    
    cincoffset c9, c9, %cheri_compartment_pccrel_lo(6b)
    li x13, 0xff7f
    candperm c9, c9, x13            # remove SR permission
    cjalr c0, 0(c9)
    nop 
    nop
scr_cont1:
    li x13, 0x11223344
    li x15, 0x3
    cspecialrw c0, mtcc, c13    
    nop
    nop
scr_cont2:
    nop
    nop
    cspecialr c8, mtcc    
    csetequalexact x9, c8, c11
    beq x9, x0, scr_fail

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, scr_fail
    csrr x13, mtval
    li   x12, 0x0798
    bne x12, x13, scr_fail


    #
    # write to mtdc
    #
    cspecialr c11, mtdc
    cspecialw mtdc,c5
    cspecialr c12, mtdc
    csetequalexact x9, c5, c12
    beq x9, x0, scr_fail
    cspecialw mtdc, c11            # restore mtdc
    cspecialr c12, mtdc
    csetequalexact x9, c11, c12
    beq x9, x0, scr_fail

    #
    # read/write an illegal SCR address
    #
7: 
    auipcc  c8, %cheri_compartment_pccrel_hi(scr_cont3)    # save original pcc/pc in C8
    cincoffset c8, c8, %cheri_compartment_pccrel_lo(7b)
    nop
    li x13, 0x11223344
    li x15, 0x3
    cspecialr c11, 22             # illegal SCR address  
    nop
    nop
scr_cont3:
    nop
    nop

    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x2
    bne x12, x13, scr_fail
    csrr x13, mtval
    li   x12, 0x0
    bne x12, x13, scr_fail

8: 
    auipcc  c8, %cheri_compartment_pccrel_hi(scr_cont4)    # save original pcc/pc in C8
    cincoffset c8, c8, %cheri_compartment_pccrel_lo(8b)
    nop
    li x13, 0x11223344
    li x15, 0x3
    cspecialw 22, c11             # illegal SCR  address 
    nop
    nop
scr_cont4:
    nop
    nop

    # this doesn't match sail for now.. QQQ
    #csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    #bne x12, x13, scr_fail
    #csrr x13, mtval
    li   x12, 0x06d8
    #bne x12, x13, scr_fail

    li a0, 0x0
    j scr_exit

scr_fail:
    li a0, 0xf8     # error code

scr_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  test misc instructions
#  ///////////////////////////////////////

test_misc_instr:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    # doon't worry about checking results here, just compare with sail
    cgetlen x11, c5
    cgetlen x12, c4
    cgetperm x11, c5
    cgetperm x12, c4
    cgettype x11, c5
    cgettype x12, c4
    j misc_0
    .align 4   
misc_0:
    # cgettop x11, c5  # compiler can't handle this???
    .word 0xff8285db
    # cgettop x12, c4  
    .word 0xff82065b
    # cgethigh x11, c5 # compiler can't handle this yet
    .word 0xff7285db
    # cgethigh x12, c4 
    .word 0xff72065b

    # csethigh c11, c4, x12   # should get c11 = c4, c11.tag = 0
    .word 0x2cc205db

    ctestsubset x11, c5, c5
    ctestsubset x11, c5, c6
    ctestsubset x11, c6, c5

    # auicgp c11, 8    # compiler can't handle this???
    .word 0x000085fb
    # auicgp c11, 0xf8123    
    .word 0xf81235fb

    addi x11, x11, 1   # let's verify the meta-data in c11 will cleared by this
    # cgethigh x12, c11 
    .word 0xff75865b

    li a0, 0x0
    j misc_exit

misc_fail:
    li a0, 0xb8     # error code

misc_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  test ASR permission (CSR/MRET case)
#  ///////////////////////////////////////

test_asr:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)                

    #
    # test CSR access wo/ ASR permission
    # 
    lui x11, %hi(asr_cont1)
    addi  x11, x11, %lo(asr_cont1)
    csetaddr c8, c4, x11
    csetaddr c9, c4, x11
    li x13, 0xff7f
    candperm c9, c9, x13            # remove SR permission
    
    li x15, 0x4
    cjalr c0, 0(c9)
    nop
    nop
asr_cont1:
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, asr_fail
    csrr x13, mtval
    li   x12, 0x0418
    bne x12, x13, asr_fail

    #
    # test MRET wo/ ASR permission
    # 
    lui x11, %hi(asr_cont2)
    addi  x11, x11, %lo(asr_cont2)
    csetaddr c8, c4, x11
    csetaddr c9, c4, x11
    li x13, 0xff7f
    candperm c9, c9, x13            # remove SR permission
    
    cspecialw mepcc, c9

    li x15, 0x5
    li x12, 0x00001800        // bit 12:11 (MPP) = 3 to stay in M-priv level
    csrs mstatus, x12         
    mret                      // jump to the new PCC

    nop
    nop
asr_cont2:
    csrr x13, mcause              # check mcause and mtval
    li   x12, 0x1c
    bne x12, x13, asr_fail
    csrr x13, mtval
    li   x12, 0x0418
    bne x12, x13, asr_fail

    li a0, 0x0
    j asr_exit

asr_fail:
    li a0, 0xe9     # error code

asr_exit:
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

    PRINTMSG x11, test_bounds_msg
    ccall test_bounds
    bne a0, x0, test_exit

    PRINTMSG x11, test_addr_msg
    ccall test_addr
    bne a0, x0, test_exit

    PRINTMSG x11, test_seal_msg
    ccall test_seal
    bne a0, x0, test_exit

    PRINTMSG x11, test_tsafe_msg
    ccall test_tsafe
    bne a0, x0, test_exit

    PRINTMSG x11, test_jump_msg
    ccall test_jump
    bne a0, x0, test_exit

    PRINTMSG x11, test_lsft_msg
    ccall test_lsft
    bne a0, x0, test_exit

    PRINTMSG x11, test_scr_msg
    ccall test_scr
    bne a0, x0, test_exit

    PRINTMSG x11, test_misc_instr_msg
    ccall test_misc_instr
    bne a0, x0, test_exit

    PRINTMSG x11, test_asr_msg
    ccall test_asr
    bne a0, x0, test_exit

    j test_exit

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
  .string "Running assembly test suite \n"
test_bounds_msg :
  .string "Testing set_bounds.. \n"
test_addr_msg :
  .string "Testing set_addr corner cases.. \n"
test_seal_msg :
  .string "Testing seal/unseal.. \n"
test_tsafe_msg :
  .string "Testing tsafe.. \n"
test_jump_msg :
  .string "Testing cjal/cjalr/jump fault.. \n"
test_lsft_msg :
  .string "Testing load/store faults.. \n"
test_scr_msg :
  .string "Testing SCR accesses.. \n"
test_misc_instr_msg :
  .string "Testing misc instructions.. \n"
test_asr_msg :
  .string "Testing ASR perm faults.. \n"

#.section .tohost
#tohost :
#  .dword 0
#fromhost :
#  .dword 0
