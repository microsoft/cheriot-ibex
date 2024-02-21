// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"


/**
 * Top level module of the ibex RISC-V core
 */
module ibex_top import ibex_pkg::*; import cheri_pkg::*; #(
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  parameter bit          DbgTriggerEn     = 1'b1,
  parameter int unsigned DbgHwBreakNum    = 2,
  parameter int unsigned MHPMCounterNum   = 0,
  parameter int unsigned MHPMCounterWidth = 40,
  parameter bit          RV32E            = 1'b0,
  parameter rv32b_e      RV32B            = RV32BNone,
  parameter bit          WritebackStage   = 1'b1,
  parameter bit          BranchPredictor  = 1'b0,
  parameter bit          SecureIbex       = 1'b0,   // placeholder for TB compatbility
  parameter bit          CHERIoTEn        = 1'b1,
  parameter int unsigned DataWidth        = 33,
  parameter int unsigned HeapBase         = 32'h2001_0000,
  parameter int unsigned TSMapBase        = 32'h2002_f000, // 4kB default
  parameter int unsigned TSMapSize        = 1024,
  parameter bit          MemCapFmt        = 1'b0,
  parameter bit          CheriPPLBC       = 1'b1,
  parameter bit          CheriSBND2       = 1'b0,
  parameter bit          CheriTBRE        = 1'b0,
  parameter int unsigned MMRegDinW        = 128,
  parameter int unsigned MMRegDoutW       = 64
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         test_en_i,     // enable all clock gates for testing
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

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output reg_cap_t                     rvfi_rs1_rcap,
  output logic [31:0]                  rvfi_rs2_rdata,
  output reg_cap_t                     rvfi_rs2_rcap,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output reg_cap_t                     rvfi_rd_wcap,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [32:0]                  rvfi_mem_rdata,
  output logic [32:0]                  rvfi_mem_wdata,
  output logic                         rvfi_mem_is_cap,
  output reg_cap_t                     rvfi_mem_rcap,
  output reg_cap_t                     rvfi_mem_wcap,
  output logic [31:0]                  rvfi_ext_mip,
  output logic                         rvfi_ext_nmi,
  output logic                         rvfi_ext_debug_req,
  output logic [63:0]                  rvfi_ext_mcycle,
`endif

  // CPU Control Signals
  input  fetch_enable_t                fetch_enable_i,
  output logic                         core_sleep_o,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,


  // DFT bypass controls
  input logic                          scan_rst_ni
);

  localparam bit          ResetAll          = 1'b1;
  localparam int unsigned RegFileDataWidth  = 32;

  // Clock signals
  logic                        clk;
  logic                        core_busy_d, core_busy_q;
  logic                        clock_en;
  logic                        irq_pending;
  // Core <-> Register file signals
  logic [4:0]                  rf_raddr_a;
  logic [4:0]                  rf_raddr_b;
  logic [4:0]                  rf_waddr_wb;
  logic                        rf_we_wb;
  logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_a_ecc, rf_rdata_a_ecc_buf;
  logic [RegFileDataWidth-1:0] rf_rdata_b_ecc, rf_rdata_b_ecc_buf;
  reg_cap_t                    rf_rcap_a, rf_rcap_b;
  reg_cap_t                    rf_wcap;

  logic [31:0]   rf_reg_rdy;
  logic [4:0]    rf_trvk_addr;
  logic          rf_trvk_en;
  logic          rf_trvk_clrtag;
  logic [4:0]    rf_trsv_addr;
  logic          rf_trsv_en;

  fetch_enable_t fetch_enable_buf;

  /////////////////////
  // Main clock gate //
  /////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_d;
    end
  end

  assign clock_en     = core_busy_q | debug_req_i | irq_pending | irq_nm_i;
  assign core_sleep_o = ~clock_en;

  // let's not worry about clock gating for now. kliu
  assign clk = clk_i;

//  prim_clock_gating core_clock_gate_i (
//    .clk_i    (clk_i),
//    .en_i     (clock_en),
//    .test_en_i(test_en_i),
//    .clk_o    (clk)
//  );

  ////////////////////////
  // Core instantiation //
  ////////////////////////

`ifdef FPGA
  // Buffer security critical signals to prevent synthesis optimisation removing them
  prim_buf #(.Width($bits(fetch_enable_t))) u_fetch_enable_buf (
    .in_i (fetch_enable_i),
    .out_o(fetch_enable_buf)
  );

  prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_a_ecc_buf (
    .in_i (rf_rdata_a_ecc),
    .out_o(rf_rdata_a_ecc_buf)
  );

  prim_buf #(.Width(RegFileDataWidth)) u_rf_rdata_b_ecc_buf (
    .in_i (rf_rdata_b_ecc),
    .out_o(rf_rdata_b_ecc_buf)
  );
`else
  assign fetch_enable_buf = fetch_enable_i;
  assign rf_rdata_a_ecc_buf = rf_rdata_a_ecc;
  assign rf_rdata_b_ecc_buf = rf_rdata_b_ecc;
`endif

  ibex_core #(
    .PMPEnable        (1'b0),
    .PMPGranularity   (0),
    .PMPNumRegions    (4),
    .MHPMCounterNum   (MHPMCounterNum  ),
    .MHPMCounterWidth (MHPMCounterWidth),
    .RV32E            (RV32E),
    .RV32M            (RV32MFast),
    .RV32B            (RV32BNone),
    .BranchTargetALU  (1'b1),
    .ICache           (1'b0),
    .ICacheECC        (1'b0),
    .BusSizeECC       (BUS_SIZE),
    .TagSizeECC       (IC_TAG_SIZE),
    .LineSizeECC      (IC_LINE_SIZE),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .WritebackStage   (WritebackStage),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeedDefault),
    .RndCnstLfsrPerm  (RndCnstLfsrPermDefault),
    .SecureIbex       (1'b0),
    .DummyInstructions(1'b0),
    .RegFileECC       (1'b0),
    .RegFileDataWidth (RegFileDataWidth),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .CHERIoTEn        (CHERIoTEn),
    .DataWidth        (DataWidth),
    .HeapBase         (HeapBase),
    .TSMapBase        (TSMapBase),
    .TSMapSize        (TSMapSize),
    .MemCapFmt        (MemCapFmt),
    .CheriPPLBC       (CheriPPLBC),
    .CheriSBND2       (CheriSBND2),
    .CheriTBRE        (CheriTBRE),
    .MMRegDinW        (MMRegDinW),
    .MMRegDoutW       (MMRegDoutW)
  ) u_ibex_core (
    .clk_i      (clk),
    .rst_ni     (rst_ni),

    .cheri_pmode_i  (cheri_pmode_i),
    .cheri_tsafe_en_i  (cheri_tsafe_en_i),
    .hart_id_i      (hart_id_i    ) ,
    .boot_addr_i    (boot_addr_i  ) ,

    .instr_req_o    (instr_req_o   ),
    .instr_gnt_i    (instr_gnt_i   ),
    .instr_rvalid_i (instr_rvalid_i),
    .instr_addr_o   (instr_addr_o  ),
    .instr_rdata_i  (instr_rdata_i ),
    .instr_err_i    (instr_err_i   ),

    .data_req_o     (data_req_o    ),
    .data_is_cap_o  (data_is_cap_o ),
    .data_gnt_i     (data_gnt_i    ),
    .data_rvalid_i  (data_rvalid_i ),
    .data_we_o      (data_we_o     ),
    .data_be_o      (data_be_o     ),
    .data_addr_o    (data_addr_o   ),
    .data_wdata_o   (data_wdata_o  ),
    .data_rdata_i   (data_rdata_i  ),
    .data_err_i     (data_err_i    ),

    .dummy_instr_id_o (),
    .rf_raddr_a_o     (rf_raddr_a),
    .rf_raddr_b_o     (rf_raddr_b),
    .rf_waddr_wb_o    (rf_waddr_wb),
    .rf_we_wb_o       (rf_we_wb),
    .rf_wdata_wb_ecc_o(rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i (rf_rdata_a_ecc_buf),
    .rf_rdata_b_ecc_i (rf_rdata_b_ecc_buf),
    .rf_wcap_wb_o     (rf_wcap),
    .rf_rcap_a_i      (rf_rcap_a),
    .rf_rcap_b_i      (rf_rcap_b),
    .rf_reg_rdy_i     (rf_reg_rdy),
    .rf_trsv_en_o     (rf_trsv_en),
    .rf_trsv_addr_o   (rf_trsv_addr),
    .rf_trvk_addr_o   (rf_trvk_addr),
    .rf_trvk_en_o     (rf_trvk_en    ),
    .rf_trvk_clrtag_o (rf_trvk_clrtag),
    .rf_trvk_par_o    (),
    .rf_trsv_par_o    (),
    .tsmap_cs_o       (tsmap_cs_o   ),
    .tsmap_addr_o     (tsmap_addr_o ),
    .tsmap_rdata_i    (tsmap_rdata_i),
    .mmreg_corein_i   (mmreg_corein_i),
    .mmreg_coreout_o  (mmreg_coreout_o),
    .cheri_fatal_err_o(cheri_fatal_err_o),

    .irq_software_i (irq_software_i),
    .irq_timer_i    (irq_timer_i   ),
    .irq_external_i (irq_external_i),
    .irq_fast_i     (irq_fast_i    ),
    .irq_nm_i       (irq_nm_i      ),
    .irq_pending_o(irq_pending),

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
    .rvfi_mem_is_cap,
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_ext_mip,
    .rvfi_ext_nmi,
    .rvfi_ext_debug_req,
    .rvfi_ext_mcycle,
`endif

    .fetch_enable_i(fetch_enable_buf),
    .alert_minor_o(),
    .alert_major_o(),
    .icache_inval_o(),
    .core_busy_o   (core_busy_d),
    .ic_scr_key_valid_i (1'b0),
    .ic_data_rdata_i    (),
    .ic_data_wdata_o    (),
    .ic_data_addr_o     (),
    .ic_data_write_o    (),
    .ic_data_req_o      (),
    .ic_tag_rdata_i     (),
    .ic_tag_wdata_o     (),
    .ic_tag_addr_o      (),
    .ic_tag_write_o     (), 
    .ic_tag_req_o       ()
  );

  assign data_wdata_intg_o = 7'h0;

  /////////////////////////////////
  // Register file Instantiation //
  /////////////////////////////////
  if (RV32E) begin
    cheri_regfile #(
      .NREGS(16),
      .NCAPS(16),
      .CheriPPLBC(CheriPPLBC)
    ) register_file_i (
      .clk_i         (clk),
      .rst_ni        (rst_ni),
      .raddr_a_i     (rf_raddr_a),
      .rdata_a_o     (rf_rdata_a_ecc),
      .rcap_a_o      (rf_rcap_a),
      .raddr_b_i     (rf_raddr_b),
      .rdata_b_o     (rf_rdata_b_ecc),
      .rcap_b_o      (rf_rcap_b),
      .waddr_a_i     (rf_waddr_wb),
      .wdata_a_i     (rf_wdata_wb_ecc),
      .wcap_a_i      (rf_wcap),
      .we_a_i        (rf_we_wb),
      .reg_rdy_o     (rf_reg_rdy),
      .trvk_addr_i   (rf_trvk_addr),
      .trvk_en_i     (rf_trvk_en),
      .trvk_clrtag_i (rf_trvk_clrtag),
      .trsv_addr_i   (rf_trsv_addr),
      .trsv_en_i     (rf_trsv_en),
      .trsv_par_i    (7'h0),
      .trvk_par_i    (7'h0),
      .par_rst_ni    (1'b0),
      .alert_o       ()
    );
  end else begin
    cheri_regfile #(
      .NREGS(32),
      .NCAPS(32),
      .CheriPPLBC(CheriPPLBC)
    ) register_file_i (
      .clk_i         (clk),
      .rst_ni        (rst_ni),
      .raddr_a_i     (rf_raddr_a),
      .rdata_a_o     (rf_rdata_a_ecc),
      .rcap_a_o      (rf_rcap_a),
      .raddr_b_i     (rf_raddr_b),
      .rdata_b_o     (rf_rdata_b_ecc),
      .rcap_b_o      (rf_rcap_b),
      .waddr_a_i     (rf_waddr_wb),
      .wdata_a_i     (rf_wdata_wb_ecc),
      .wcap_a_i      (rf_wcap),
      .we_a_i        (rf_we_wb),
      .reg_rdy_o     (rf_reg_rdy),
      .trvk_addr_i   (rf_trvk_addr),
      .trvk_en_i     (rf_trvk_en),
      .trvk_clrtag_i (rf_trvk_clrtag),
      .trsv_addr_i   (rf_trsv_addr),
      .trsv_en_i     (rf_trsv_en),
      .trsv_par_i    (7'h0),
      .trvk_par_i    (7'h0),
      .par_rst_ni    (1'b0),
      .alert_o       ()
    );
  end

endmodule
