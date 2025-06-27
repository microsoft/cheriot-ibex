
.section .text

.globl default_handler
.globl _start

_start: 
        li sp, 0x8001ff00      # setup sp

#       mtvec writes doesn't work on ibex right now
#1:      auipc   t0, %pcrel_hi(mtvec)        # load mtvec(hi)
#        addi    t0, t0, %pcrel_lo(1b)       # load mtvec(lo)
#        csrrw   zero, mtvec, t0

        li t0,  0x88                        # set mstatus.mie=1, mstatus.mpie=1
        csrrs zero, mstatus, t0 
        li t0,  0x1800                      # set mstatus.mpp=00
        csrrc zero, mstatus, t0 

#        #?? set mret return address
#1:      auipc   t0, %pcrel_hi(cont1)
#        addi    t0, t0, %pcrel_lo(1b)
#        csrrw   zero, mepc, t0
        
#        mret
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

     call cstart 

w3:    j w3 

default_handler:  
        mret

