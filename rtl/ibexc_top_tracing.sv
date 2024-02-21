// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Top level module of the ibex RISC-V core with tracing enabled
 */

module ibex_top_tracing import ibex_pkg::*; import cheri_pkg::*; #(
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  parameter int unsigned HeapBase         = 32'h2001_0000,
  parameter int unsigned TSMapBase        = 32'h2004_0000, // 4kB default
  parameter int unsigned TSMapSize        = 1024,          // in words
  parameter int unsigned MMRegDinW        = 128,
  parameter int unsigned MMRegDoutW       = 64,
  parameter int unsigned DataWidth        = 33      // this enables testbench to use defparam to override
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         test_en_i,     // enable all clock gates for testing
  input  logic                         scan_rst_ni,
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input  logic                         cheri_pmode_i,
  input  logic                         cheri_tsafe_en_i,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [31:0]                  instr_rdata_i,
  input  logic [6:0]                   instr_rdata_intg_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  output logic                         data_is_cap_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [32:0]                  data_wdata_o,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [32:0]                  data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  // TS map memory interface
  output logic                         tsmap_cs_o,
  output logic [15:0]                  tsmap_addr_o,
  input  logic [31:0]                  tsmap_rdata_i,
  input  logic [6:0]                   tsmap_rdata_intg_i,   // not used in ibexc_top
  input  logic [MMRegDinW-1:0]         mmreg_corein_i,
  output logic [MMRegDoutW-1:0]        mmreg_coreout_o,
  output logic                         cheri_fatal_err_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt

  // Scrambling Interface
  input  logic                         scramble_key_valid_i,
  input  logic [SCRAMBLE_KEY_W-1:0]    scramble_key_i,
  input  logic [SCRAMBLE_NONCE_W-1:0]  scramble_nonce_i,
  output logic                         scramble_req_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  output logic                         double_fault_seen_o,

  // CPU Control Signals
  input  fetch_enable_t                fetch_enable_i,
  output logic                         core_sleep_o
);


  logic        rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic        rvfi_trap;
  logic        rvfi_halt;
  logic        rvfi_intr;
  logic [ 1:0] rvfi_mode;
  logic [ 1:0] rvfi_ixl;
  logic [ 4:0] rvfi_rs1_addr;
  logic [ 4:0] rvfi_rs2_addr;
  logic [ 4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  reg_cap_t    rvfi_rs1_rcap;
  reg_cap_t    rvfi_rs2_rcap;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [ 4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  reg_cap_t    rvfi_rd_wcap;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [ 3:0] rvfi_mem_rmask;
  logic [ 3:0] rvfi_mem_wmask;
  logic [DataWidth-1:0] rvfi_mem_rdata;
  logic [DataWidth-1:0] rvfi_mem_wdata;
  logic        rvfi_mem_is_cap;
  reg_cap_t     rvfi_mem_rcap;
  reg_cap_t     rvfi_mem_wcap;
  logic [31:0] rvfi_ext_mip;
  logic        rvfi_ext_nmi;
  logic        rvfi_ext_debug_req;
  logic [63:0] rvfi_ext_mcycle;

  logic [31:0] unused_rvfi_ext_mip;
  logic        unused_rvfi_ext_nmi;
  logic        unused_rvfi_ext_debug_req;
  logic [63:0] unused_rvfi_ext_mcycle;

  // Tracer doesn't use these signals, though other modules may probe down into tracer to observe
  // them.
  assign unused_rvfi_ext_mip = rvfi_ext_mip;
  assign unused_rvfi_ext_nmi = rvfi_ext_nmi;
  assign unused_rvfi_ext_debug_req = rvfi_ext_debug_req;
  assign unused_rvfi_ext_mcycle = rvfi_ext_mcycle;

  ibex_top #(
    .DmHaltAddr       (DmHaltAddr       ),
    .DmExceptionAddr  (DmExceptionAddr  ),
    .MHPMCounterNum   (13  ),
    .MHPMCounterWidth (40),
    .DbgTriggerEn     (1'b1),
    .DbgHwBreakNum    (4),
    .RV32E            (1'b0),
    .RV32B            (RV32BFull),
    .WritebackStage   (1'b1),
    .BranchPredictor  (1'b0),
    .CHERIoTEn        (1'b1),
    .DataWidth        (DataWidth),
    .HeapBase         (HeapBase ),
    .TSMapBase        (TSMapBase),
    .TSMapSize        (TSMapSize),
    .MemCapFmt        (1'b0),
    .CheriPPLBC       (1'b1),
    .CheriSBND2       (1'b0),
    .CheriTBRE        (1'b1),
    .MMRegDinW        (MMRegDinW),
    .MMRegDoutW       (MMRegDoutW)
  ) u_ibex_top (
    .clk_i,
    .rst_ni,

    .test_en_i,
    .scan_rst_ni,
    .ram_cfg_i,

    .cheri_pmode_i,
    .cheri_tsafe_en_i,
    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_rdata_intg_i,
    .instr_err_i,

    .data_req_o,
    .data_is_cap_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_wdata_intg_o,
    .data_rdata_i,
    .data_rdata_intg_i,
    .data_err_i,

    .tsmap_cs_o,
    .tsmap_addr_o,
    .tsmap_rdata_i,
    .mmreg_corein_i,
    .mmreg_coreout_o,
    .cheri_fatal_err_o,

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,

    .scramble_key_valid_i,
    .scramble_key_i,
    .scramble_nonce_i,
    .scramble_req_o,

    .debug_req_i,
    .crash_dump_o,
    .double_fault_seen_o,

`ifdef RVFI
    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs1_rcap,
    .rvfi_rs2_rdata,
    .rvfi_rs2_rcap,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_rd_wcap,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_mem_is_cap,
    .rvfi_ext_mip,
    .rvfi_ext_nmi,
    .rvfi_ext_debug_req,
    .rvfi_ext_mcycle,
`endif
    .fetch_enable_i,
    .core_sleep_o,
    .alert_major_bus_o(),
    .alert_major_internal_o(),
    .alert_minor_o()
  );

// ibex_tracer relies on the signals from the RISC-V Formal Interface
// synthesis translate_off
`ifndef RVFI
   $fatal("Fatal error: RVFI needs to be defined globally.");
`endif

`ifdef RVFI
  ibex_tracer #(
    .DataWidth        (DataWidth)
  ) u_ibex_tracer (
    .clk_i,
    .rst_ni,

    .cheri_pmode_i,
    .cheri_tsafe_en_i,
    .hart_id_i,

    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rs1_rcap,
    .rvfi_rs2_rcap,
    .rvfi_rd_wcap,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_mem_is_cap
  );
`endif

// synthesis translate_on

endmodule
