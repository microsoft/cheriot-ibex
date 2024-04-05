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
#  init
#  ///////////////////////////////////////

test_init:

    cspecialrw c3, 29, c0    # read MTDC address 'd29, memory root

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

    li x11, 0x83800100        # write to this location to tell TB end of init
    csetaddr c8, c6, x11 
    li x11, 0xf               # enable all faults/interrupts
    csw x11, (c8)

    li x9, 0x800              # enable machine-mode ext/tmr/sw interrupts
    csrs mie, x9

    li a0, 0x0
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
  .string "Doing something in assembly..\n"

#.section .tohost
#tohost :
#  .dword 0
#fromhost :
#  .dword 0
