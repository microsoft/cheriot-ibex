// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csr_pkg;

 // Privileged mode
  typedef enum logic[1:0] {
    PRIV_LVL_M = 2'b11,
    PRIV_LVL_H = 2'b10,
    PRIV_LVL_S = 2'b01,
    PRIV_LVL_U = 2'b00
  } priv_lvl_e;

  // CSR operations
  typedef enum logic [1:0] {
    CSR_OP_READ,
    CSR_OP_WRITE,
    CSR_OP_SET,
    CSR_OP_CLEAR
  } csr_op_e;

  // CSRs
  typedef enum logic[11:0] {
    // Machine information
    CSR_MVENDORID = 12'hF11,
    CSR_MARCHID   = 12'hF12,
    CSR_MIMPID    = 12'hF13,
    CSR_MHARTID   = 12'hF14,

    // Machine trap setup
    CSR_MSTATUS   = 12'h300,
    CSR_MISA      = 12'h301,
    CSR_MIE       = 12'h304,
    CSR_MTVEC     = 12'h305,
    CSR_MCOUNTEREN= 12'h306,

    // Machine trap handling
    CSR_MSCRATCH  = 12'h340,
    CSR_MEPC      = 12'h341,
    CSR_MCAUSE    = 12'h342,
    CSR_MTVAL     = 12'h343,
    CSR_MIP       = 12'h344,

    // Physical memory protection
    CSR_PMPCFG0   = 12'h3A0,
    CSR_PMPCFG1   = 12'h3A1,
    CSR_PMPCFG2   = 12'h3A2,
    CSR_PMPCFG3   = 12'h3A3,
    CSR_PMPADDR0  = 12'h3B0,
    CSR_PMPADDR1  = 12'h3B1,
    CSR_PMPADDR2  = 12'h3B2,
    CSR_PMPADDR3  = 12'h3B3,
    CSR_PMPADDR4  = 12'h3B4,
    CSR_PMPADDR5  = 12'h3B5,
    CSR_PMPADDR6  = 12'h3B6,
    CSR_PMPADDR7  = 12'h3B7,

    CSR_PMPADDR8  = 12'h3B8,
    CSR_PMPADDR9  = 12'h3B9,
    CSR_PMPADDR10 = 12'h3BA,
    CSR_PMPADDR11 = 12'h3BB,
    CSR_PMPADDR12 = 12'h3BC,
    CSR_PMPADDR13 = 12'h3BD,
    CSR_PMPADDR14 = 12'h3BE,
    CSR_PMPADDR15 = 12'h3BF,

    // ePMP control
    CSR_MSECCFG   = 12'h747,
    CSR_MSECCFGH  = 12'h757,

    // Debug trigger
    CSR_TSELECT   = 12'h7A0,
    CSR_TDATA1    = 12'h7A1,
    CSR_TDATA2    = 12'h7A2,
    CSR_TDATA3    = 12'h7A3,
    CSR_MCONTEXT  = 12'h7A8,
    CSR_SCONTEXT  = 12'h7AA,

    // Debug/trace
    CSR_DCSR      = 12'h7b0,
    CSR_DPC       = 12'h7b1,

    // Debug
    CSR_DSCRATCH0 = 12'h7b2, // optional
    CSR_DSCRATCH1 = 12'h7b3, // optional

    // Machine Counter/Timers
    CSR_MCOUNTINHIBIT  = 12'h320,
    CSR_MHPMEVENT3     = 12'h323,
    CSR_MHPMEVENT4     = 12'h324,
    CSR_MHPMEVENT5     = 12'h325,
    CSR_MHPMEVENT6     = 12'h326,
    CSR_MHPMEVENT7     = 12'h327,
    CSR_MHPMEVENT8     = 12'h328,
    CSR_MHPMEVENT9     = 12'h329,
    CSR_MHPMEVENT10    = 12'h32A,
    CSR_MHPMEVENT11    = 12'h32B,
    CSR_MHPMEVENT12    = 12'h32C,
    CSR_MHPMEVENT13    = 12'h32D,
    CSR_MHPMEVENT14    = 12'h32E,
    CSR_MHPMEVENT15    = 12'h32F,
    CSR_MHPMEVENT16    = 12'h330,
    CSR_MHPMEVENT17    = 12'h331,
    CSR_MHPMEVENT18    = 12'h332,
    CSR_MHPMEVENT19    = 12'h333,
    CSR_MHPMEVENT20    = 12'h334,
    CSR_MHPMEVENT21    = 12'h335,
    CSR_MHPMEVENT22    = 12'h336,
    CSR_MHPMEVENT23    = 12'h337,
    CSR_MHPMEVENT24    = 12'h338,
    CSR_MHPMEVENT25    = 12'h339,
    CSR_MHPMEVENT26    = 12'h33A,
    CSR_MHPMEVENT27    = 12'h33B,
    CSR_MHPMEVENT28    = 12'h33C,
    CSR_MHPMEVENT29    = 12'h33D,
    CSR_MHPMEVENT30    = 12'h33E,
    CSR_MHPMEVENT31    = 12'h33F,
    CSR_MCYCLE         = 12'hB00,
    CSR_MINSTRET       = 12'hB02,
    CSR_MHPMCOUNTER3   = 12'hB03,
    CSR_MHPMCOUNTER4   = 12'hB04,
    CSR_MHPMCOUNTER5   = 12'hB05,
    CSR_MHPMCOUNTER6   = 12'hB06,
    CSR_MHPMCOUNTER7   = 12'hB07,
    CSR_MHPMCOUNTER8   = 12'hB08,
    CSR_MHPMCOUNTER9   = 12'hB09,
    CSR_MHPMCOUNTER10  = 12'hB0A,
    CSR_MHPMCOUNTER11  = 12'hB0B,
    CSR_MHPMCOUNTER12  = 12'hB0C,
    CSR_MHPMCOUNTER13  = 12'hB0D,
    CSR_MHPMCOUNTER14  = 12'hB0E,
    CSR_MHPMCOUNTER15  = 12'hB0F,
    CSR_MHPMCOUNTER16  = 12'hB10,
    CSR_MHPMCOUNTER17  = 12'hB11,
    CSR_MHPMCOUNTER18  = 12'hB12,
    CSR_MHPMCOUNTER19  = 12'hB13,
    CSR_MHPMCOUNTER20  = 12'hB14,
    CSR_MHPMCOUNTER21  = 12'hB15,
    CSR_MHPMCOUNTER22  = 12'hB16,
    CSR_MHPMCOUNTER23  = 12'hB17,
    CSR_MHPMCOUNTER24  = 12'hB18,
    CSR_MHPMCOUNTER25  = 12'hB19,
    CSR_MHPMCOUNTER26  = 12'hB1A,
    CSR_MHPMCOUNTER27  = 12'hB1B,
    CSR_MHPMCOUNTER28  = 12'hB1C,
    CSR_MHPMCOUNTER29  = 12'hB1D,
    CSR_MHPMCOUNTER30  = 12'hB1E,
    CSR_MHPMCOUNTER31  = 12'hB1F,
    CSR_MCYCLEH        = 12'hB80,
    CSR_MINSTRETH      = 12'hB82,
    CSR_MHPMCOUNTER3H  = 12'hB83,
    CSR_MHPMCOUNTER4H  = 12'hB84,
    CSR_MHPMCOUNTER5H  = 12'hB85,
    CSR_MHPMCOUNTER6H  = 12'hB86,
    CSR_MHPMCOUNTER7H  = 12'hB87,
    CSR_MHPMCOUNTER8H  = 12'hB88,
    CSR_MHPMCOUNTER9H  = 12'hB89,
    CSR_MHPMCOUNTER10H = 12'hB8A,
    CSR_MHPMCOUNTER11H = 12'hB8B,
    CSR_MHPMCOUNTER12H = 12'hB8C,
    CSR_MHPMCOUNTER13H = 12'hB8D,
    CSR_MHPMCOUNTER14H = 12'hB8E,
    CSR_MHPMCOUNTER15H = 12'hB8F,
    CSR_MHPMCOUNTER16H = 12'hB90,
    CSR_MHPMCOUNTER17H = 12'hB91,
    CSR_MHPMCOUNTER18H = 12'hB92,
    CSR_MHPMCOUNTER19H = 12'hB93,
    CSR_MHPMCOUNTER20H = 12'hB94,
    CSR_MHPMCOUNTER21H = 12'hB95,
    CSR_MHPMCOUNTER22H = 12'hB96,
    CSR_MHPMCOUNTER23H = 12'hB97,
    CSR_MHPMCOUNTER24H = 12'hB98,
    CSR_MHPMCOUNTER25H = 12'hB99,
    CSR_MHPMCOUNTER26H = 12'hB9A,
    CSR_MHPMCOUNTER27H = 12'hB9B,
    CSR_MHPMCOUNTER28H = 12'hB9C,
    CSR_MHPMCOUNTER29H = 12'hB9D,
    CSR_MHPMCOUNTER30H = 12'hB9E,
    CSR_MHPMCOUNTER31H = 12'hB9F,
    CSR_MSHWM          = 12'hBC1,
    CSR_MSHWMB         = 12'hBC2,
    CSR_CDBG_CTRL      = 12'hBC4,
    CSR_CPUCTRL        = 12'h7C0,
    CSR_SECURESEED     = 12'h7C1
  } csr_num_e;

  typedef struct packed {
    logic        irq_software;
    logic        irq_timer;
    logic        irq_external;
    logic [14:0] irq_fast; // 15 fast interrupts,
                          // one interrupt is reserved for NMI (not visible through mip/mie)
  } irqs_t;

  // Exception cause
  typedef enum logic [5:0] {
    EXC_CAUSE_IRQ_SOFTWARE_M      = {1'b1, 5'd03},
    EXC_CAUSE_IRQ_TIMER_M         = {1'b1, 5'd07},
    EXC_CAUSE_IRQ_EXTERNAL_M      = {1'b1, 5'd11},
    // EXC_CAUSE_IRQ_FAST_0       = {1'b1, 5'd16},
    // EXC_CAUSE_IRQ_FAST_14      = {1'b1, 5'd30},
    EXC_CAUSE_IRQ_NM              = {1'b1, 5'd31}, // == EXC_CAUSE_IRQ_FAST_15
    EXC_CAUSE_INSN_ADDR_MISA      = {1'b0, 5'd00},
    EXC_CAUSE_INSTR_ACCESS_FAULT  = {1'b0, 5'd01},
    EXC_CAUSE_ILLEGAL_INSN        = {1'b0, 5'd02},
    EXC_CAUSE_BREAKPOINT          = {1'b0, 5'd03},
    EXC_CAUSE_LOAD_ADDR_MISALIGN  = {1'b0, 5'd04},
    EXC_CAUSE_LOAD_ACCESS_FAULT   = {1'b0, 5'd05},
    EXC_CAUSE_STORE_ADDR_MISALIGN = {1'b0, 5'd06},
    EXC_CAUSE_STORE_ACCESS_FAULT  = {1'b0, 5'd07},
    EXC_CAUSE_ECALL_UMODE         = {1'b0, 5'd08},
    EXC_CAUSE_ECALL_MMODE         = {1'b0, 5'd11},
    EXC_CAUSE_CHERI_FAULT         = {1'b0, 5'd28}
  } exc_cause_e;

  // Debug cause
  typedef enum logic [2:0] {
    DBG_CAUSE_NONE    = 3'h0,
    DBG_CAUSE_EBREAK  = 3'h1,
    DBG_CAUSE_TRIGGER = 3'h2,
    DBG_CAUSE_HALTREQ = 3'h3,
    DBG_CAUSE_STEP    = 3'h4
  } dbg_cause_e;

  // PMP constants
  parameter int unsigned PMP_MAX_REGIONS      = 16;
  parameter int unsigned PMP_CFG_W            = 8;

  // PMP acces type
  parameter int unsigned PMP_I  = 0;
  parameter int unsigned PMP_I2 = 1;
  parameter int unsigned PMP_D  = 2;

  typedef enum logic [1:0] {
    PMP_ACC_EXEC    = 2'b00,
    PMP_ACC_WRITE   = 2'b01,
    PMP_ACC_READ    = 2'b10
  } pmp_req_e;

  // PMP cfg structures
  typedef enum logic [1:0] {
    PMP_MODE_OFF   = 2'b00,
    PMP_MODE_TOR   = 2'b01,
    PMP_MODE_NA4   = 2'b10,
    PMP_MODE_NAPOT = 2'b11
  } pmp_cfg_mode_e;

  typedef struct packed {
    logic          lock;
    pmp_cfg_mode_e mode;
    logic          exec;
    logic          write;
    logic          read;
  } pmp_cfg_t;

  // Machine Security Configuration (ePMP)
  typedef struct packed {
    logic rlb;  // Rule Locking Bypass
    logic mmwp; // Machine Mode Whitelist Policy
    logic mml;  // Machine Mode Lockdown
  } pmp_mseccfg_t;

  // Constants for the dcsr.xdebugver fields
  typedef enum logic[3:0] {
    XDEBUGVER_NO     = 4'd0, // no external debug support
    XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
    XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
  } x_debug_ver_e;

 // CSR pmp-related offsets
  parameter logic [11:0] CSR_OFF_PMP_CFG  = 12'h3A0; // pmp_cfg  @ 12'h3a0 - 12'h3a3
  parameter logic [11:0] CSR_OFF_PMP_ADDR = 12'h3B0; // pmp_addr @ 12'h3b0 - 12'h3bf

  // CSR status bits
  parameter int unsigned CSR_MSTATUS_MIE_BIT      = 3;
  parameter int unsigned CSR_MSTATUS_MPIE_BIT     = 7;
  parameter int unsigned CSR_MSTATUS_MPP_BIT_LOW  = 11;
  parameter int unsigned CSR_MSTATUS_MPP_BIT_HIGH = 12;
  parameter int unsigned CSR_MSTATUS_MPRV_BIT     = 17;
  parameter int unsigned CSR_MSTATUS_TW_BIT       = 21;

  // CSR machine ISA
  parameter logic [1:0] CSR_MISA_MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32

  // CSR interrupt pending/enable bits
  parameter int unsigned CSR_MSIX_BIT      = 3;
  parameter int unsigned CSR_MTIX_BIT      = 7;
  parameter int unsigned CSR_MEIX_BIT      = 11;
  parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
  parameter int unsigned CSR_MFIX_BIT_HIGH = 30;

  // CSR Machine Security Configuration bits
  parameter int unsigned CSR_MSECCFG_MML_BIT  = 0;
  parameter int unsigned CSR_MSECCFG_MMWP_BIT = 1;
  parameter int unsigned CSR_MSECCFG_RLB_BIT  = 2;

  // Vendor ID
  // No JEDEC ID has been allocated to lowRISC so the value is 0 to indicate the field is not
  // implemented
  localparam logic [31:0] CSR_MVENDORID_VALUE  = 32'b0;
  localparam logic [31:0] CSR_MVENDORID_CHERI_VALUE  = 32'h255;

  // Architecture ID
  // Top bit is unset to indicate an open source project. The lower bits are an ID allocated by the
  // RISC-V Foundation. Note this is allocated specifically to Ibex, should significant changes be
  // made a different architecture ID should be supplied.
  localparam logic [31:0] CSR_MARCHID_VALUE = {1'b0, 31'd22};
  localparam logic [31:0] CSR_MARCHID_CHERI_VALUE = 32'hce1;


  // Implementation ID
  // 0 indicates this field is not implemeted. Ibex implementors may wish to indicate an RTL/netlist
  // version here using their own unique encoding (e.g. 32 bits of the git hash of the implemented
  // commit).
  localparam logic [31:0] CSR_MIMPID_VALUE = 32'b0;

endpackage
