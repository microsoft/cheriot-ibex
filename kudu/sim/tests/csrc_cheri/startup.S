.section .text
.globl _start
.globl mtvec

#.extern cheri_fault_handler

.macro LA_ABS reg, symbol
    lui             \reg, %hi(\symbol)
    addi            \reg, \reg, %lo(\symbol)
.endm

_start: 
        cspecialr c3, mtdc  # read MTDC address 'd29 (the SL root should be in MTCC which is 28, but how the roots work will change, so probably not worth fixing)
        li x11, 0x8001fff0       # setup sp
        csetaddr csp, c3, x11

        
        # cspecialr ct0, mtcc    
1:      auipcc  ct1, %cheri_compartment_pccrel_hi(mtvec)
        cincoffset ct1, ct1, %cheri_compartment_pccrel_lo(1b)

        #csetaddr ct0, ct0, t1
        #cspecialw mtcc, ct0       
        cspecialw mtcc, ct1       

        li t0,  0x88                        # set mstatus.mie=1, mstatus.mpie=1
        csrs mstatus, t0 
        li t0,  0x1800                      # set mstatus.mpp=00
        csrc mstatus, t0 


        # We now build the $cgp register. All read-write globals live here.
        cspecialr ca0, mtdc
        # Load the absolute addresses.
        LA_ABS a1, __cgp_start
        LA_ABS a2, __cgp_end
        sub a2, a2, a1 # a2 now contains the length of $cgp.
        csetaddr ct0, ca0, a1
        csetbounds ct0, ct0, a2
        srli a2, a2, 1 # $cgp needs to be biased by half of its length.
        cincoffset cgp, ct0, a2

#.option nocapmode
        #la a2, __cap_relocs
        LA_ABS a2, __cap_relocs
        csetaddr ca1, ca0, a2
        #la a3, __cap_relocs_end
        LA_ABS a3, __cap_relocs_end
#.option capmode
        sub a2, a3, a2
        li a3, 20
        divu a2, a2, a3
       
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
cont1:  nop
        nop
        nop

        # Pass the global root as the first argument, in ca0.
        # Double check if the global root is in mtdc!
        ccall cstart 

w3:    j w3 

.align 4

#
# default exception handler
#
mtvec:  
        cincoffset csp, csp, -16    # SP-16
        csc ct0, 0(csp)
        csc ct1, 8(csp)

        #ccall cheri_fault_handler

        csrr t0, mcause         // is this an interrupt or exception
        li t1, 0x80000000
        and t0, t0, t1
        beq t0, x0, mtvec_done

        li t1, 0x83800104       // acknowledge interrupts
        cspecialr ct0, mtdc
        csetaddr ct0, ct0, t1
        li t1, 0x3
        csw t1, (ct0)

mtvec_done:
        clc ct0, 0(csp)
        clc ct1, 8(csp)
        cincoffset csp, csp, 16    # SP-16

        mret

