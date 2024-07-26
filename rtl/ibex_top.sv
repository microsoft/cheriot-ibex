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
  parameter bit          PMPEnable        = 1'b0,
  parameter int unsigned PMPGranularity   = 0,
  parameter int unsigned PMPNumRegions    = 4,
  parameter int unsigned MHPMCounterNum   = 0,
  parameter int unsigned MHPMCounterWidth = 40,
  parameter bit          RV32E            = 1'b0,
  parameter rv32m_e      RV32M            = RV32MFast,
  parameter rv32b_e      RV32B            = RV32BNone,
  parameter regfile_e    RegFile          = RegFileFF,
  parameter bit          BranchTargetALU  = 1'b0,
  parameter bit          WritebackStage   = 1'b0,
  parameter bit          ICache           = 1'b0,
  parameter bit          ICacheECC        = 1'b0,
  parameter bit          BranchPredictor  = 1'b0,
  parameter bit          DbgTriggerEn     = 1'b0,
  parameter int unsigned DbgHwBreakNum    = 1,
  parameter bit          SecureIbex       = 1'b0,
  parameter bit          ICacheScramble   = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  // Default seed and nonce for scrambling
  parameter logic [SCRAMBLE_KEY_W-1:0]   RndCnstIbexKey   = RndCnstIbexKeyDefault,
  parameter logic [SCRAMBLE_NONCE_W-1:0] RndCnstIbexNonce = RndCnstIbexNonceDefault,
  // CHERIoT paramters
  parameter bit          CHERIoTEn        = 1'b1,
  parameter int unsigned DataWidth        = 33,
  parameter int unsigned HeapBase         = 32'h2001_0000,
  parameter int unsigned TSMapBase        = 32'h2002_f000, // 4kB default
  parameter int unsigned TSMapSize        = 1024,           // 32-bit words
  parameter bit          MemCapFmt        = 1'b0,
  parameter bit          CheriPPLBC       = 1'b1,
  parameter bit          CheriSBND2       = 1'b0,
  parameter bit          CheriTBRE        = 1'b1,
  parameter bit          CheriStkZ        = 1'b1,
  parameter int unsigned MMRegDinW         = 128,
  parameter int unsigned MMRegDoutW        = 64
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
  output logic [DataWidth-1:0]         data_wdata_o,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [DataWidth-1:0]         data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  // TS map memory interface
  output logic                         tsmap_cs_o,
  output logic [15:0]                  tsmap_addr_o,
  input  logic [31:0]                  tsmap_rdata_i,
  input  logic [6:0]                   tsmap_rdata_intg_i,
  input  logic [MMRegDinW-1:0]         mmreg_corein_i,
  output logic [MMRegDoutW-1:0]        mmreg_coreout_o,

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
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output reg_cap_t                     rvfi_rs1_rcap,
  output reg_cap_t                     rvfi_rs2_rcap,
  output reg_cap_t                     rvfi_rd_wcap,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [DataWidth-1:0]         rvfi_mem_rdata,
  output logic [DataWidth-1:0]         rvfi_mem_wdata,
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
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         core_sleep_o,

  // DFT bypass controls
  input logic                          scan_rst_ni
);

  localparam bit          Lockstep          = SecureIbex;
  localparam bit          ResetAll          = Lockstep;
  localparam bit          DummyInstructions = SecureIbex;
  localparam bit          RegFileECC        = SecureIbex;
  localparam int unsigned RegFileDataWidth  = RegFileECC ? 32 + 7 : 32;
  // Icache parameters
  localparam int unsigned BusSizeECC        = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC       = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC        = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;
  // Scrambling Parameter
  localparam int unsigned NumAddrScrRounds  = ICacheScramble ? 2 : 0;
  localparam int unsigned NumDiffRounds     = NumAddrScrRounds;

  // Clock signals
  logic                        clk;
  logic                        core_busy_d, core_busy_q;
  logic                        clock_en;
  logic                        irq_pending;
  // Core <-> Register file signals
  logic                        dummy_instr_id;
  logic [4:0]                  rf_raddr_a;
  logic [4:0]                  rf_raddr_b;
  logic [4:0]                  rf_waddr_wb;
  logic                        rf_we_wb;
  logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_a_ecc, rf_rdata_a_ecc_buf;
  logic [RegFileDataWidth-1:0] rf_rdata_b_ecc, rf_rdata_b_ecc_buf;
  reg_cap_t                    rf_rcap_a, rf_rcap_b;
  reg_cap_t                    rf_wcap;

  // Core <-> RAMs signals
  logic [IC_NUM_WAYS-1:0]      ic_tag_req;
  logic                        ic_tag_write;
  logic [IC_INDEX_W-1:0]       ic_tag_addr;
  logic [TagSizeECC-1:0]       ic_tag_wdata;
  logic [TagSizeECC-1:0]       ic_tag_rdata [IC_NUM_WAYS];
  logic [IC_NUM_WAYS-1:0]      ic_data_req;
  logic                        ic_data_write;
  logic [IC_INDEX_W-1:0]       ic_data_addr;
  logic [LineSizeECC-1:0]      ic_data_wdata;
  logic [LineSizeECC-1:0]      ic_data_rdata [IC_NUM_WAYS];
  // Alert signals
  logic                        core_alert_major, core_alert_minor;
  logic                        lockstep_alert_major_internal, lockstep_alert_major_bus;
  logic                        lockstep_alert_minor;
  // Scramble signals
  logic                         icache_inval;
  logic [SCRAMBLE_KEY_W-1:0]    scramble_key_q;
  logic [SCRAMBLE_NONCE_W-1:0]  scramble_nonce_q;
  logic                         scramble_key_valid_d, scramble_key_valid_q;
  logic                         scramble_req_d, scramble_req_q;

  fetch_enable_t fetch_enable_buf;

  logic [31:0]   rf_reg_rdy;
  logic [4:0]    rf_trvk_addr;
  logic          rf_trvk_en;
  logic          rf_trvk_clrtag;
  logic [6:0]    rf_trvk_par;
  logic [4:0]    rf_trsv_addr;
  logic          rf_trsv_en;
  logic [6:0]    rf_trsv_par;
  logic          rf_alert;

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

  prim_clock_gating core_clock_gate_i (
    .clk_i    (clk_i),
    .en_i     (clock_en),
    .test_en_i(test_en_i),
    .clk_o    (clk)
  );

  ////////////////////////
  // Core instantiation //
  ////////////////////////

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

  ibex_core #(
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .BranchTargetALU  (BranchTargetALU),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .WritebackStage   (WritebackStage),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .SecureIbex       (SecureIbex),
    .DummyInstructions(DummyInstructions),
    .RegFileECC       (RegFileECC),
    .RegFileDataWidth (RegFileDataWidth),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .CHERIoTEn        (CHERIoTEn),
    .DataWidth        (DataWidth),
    .HeapBase         (HeapBase   ),
    .TSMapBase        (TSMapBase  ),
    .TSMapSize        (TSMapSize),
    .MemCapFmt        (MemCapFmt   ),
    .CheriPPLBC       (CheriPPLBC),
    .CheriSBND2       (CheriSBND2),
    .CheriTBRE        (CheriTBRE),
    .CheriStkZ        (CheriStkZ)
  ) u_ibex_core (
    .clk_i(clk),
    .rst_ni,

    .hart_id_i,
    .boot_addr_i,
    .cheri_pmode_i,
    .cheri_tsafe_en_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_err_i,

    .data_req_o,
    .data_is_cap_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_rdata_i,
    .data_err_i,

    .dummy_instr_id_o (dummy_instr_id),
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
    .rf_trsv_par_o    (rf_trsv_par),
    .rf_trvk_addr_o   (rf_trvk_addr),
    .rf_trvk_en_o     (rf_trvk_en    ),
    .rf_trvk_clrtag_o (rf_trvk_clrtag),
    .rf_trvk_par_o    (rf_trvk_par),
    .tsmap_cs_o,
    .tsmap_addr_o,
    .tsmap_rdata_i,
    .mmreg_corein_i,
    .mmreg_coreout_o,

    .ic_tag_req_o      (ic_tag_req),
    .ic_tag_write_o    (ic_tag_write),
    .ic_tag_addr_o     (ic_tag_addr),
    .ic_tag_wdata_o    (ic_tag_wdata),
    .ic_tag_rdata_i    (ic_tag_rdata),
    .ic_data_req_o     (ic_data_req),
    .ic_data_write_o   (ic_data_write),
    .ic_data_addr_o    (ic_data_addr),
    .ic_data_wdata_o   (ic_data_wdata),
    .ic_data_rdata_i   (ic_data_rdata),
    .ic_scr_key_valid_i(scramble_key_valid_q),

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,
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
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_mem_is_cap,
    .rvfi_ext_mip,
    .rvfi_ext_nmi,
    .rvfi_ext_debug_req,
    .rvfi_ext_mcycle,
`endif

    .fetch_enable_i(fetch_enable_buf),
    .alert_minor_o (core_alert_minor),
    .alert_major_o (core_alert_major),
    .icache_inval_o(icache_inval),
    .core_busy_o   (core_busy_d)
  );

  /////////////////////////////////
  // Register file Instantiation //
  /////////////////////////////////
  if (!CHERIoTEn) begin
    assign rf_alert = 1'b0;     // rf_alert only available in cheri_regfile
  end

  if (CHERIoTEn) begin : gen_regfile_cheriot

    localparam int unsigned NRegs = RV32E? 16 : 32;
    localparam int unsigned NCaps = 16;

    cheri_regfile #(
      .NREGS     (NRegs),
      .NCAPS     (NCaps),
      .RegFileECC(RegFileECC),
      .DataWidth (RegFileDataWidth),
      .CheriPPLBC(CheriPPLBC)
    ) register_file_i (
      .clk_i         (clk),
      .rst_ni        (rst_ni),
      .par_rst_ni    (rst_ni),
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
      .trvk_par_i    (rf_trvk_par),
      .trsv_addr_i   (rf_trsv_addr),
      .trsv_en_i     (rf_trsv_en),
      .trsv_par_i    (rf_trsv_par),
      .alert_o       (rf_alert)
    );

  end else if (RegFile == RegFileFF) begin : gen_regfile_ff
    ibex_register_file_ff #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb)
    );

    assign rf_rcap_a  = NULL_REG_CAP;
    assign rf_rcap_b  = NULL_REG_CAP;
    assign rf_reg_rdy = {32{1'b1}};

  end else if (RegFile == RegFileFPGA) begin : gen_regfile_fpga
    ibex_register_file_fpga #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb)
    );

    assign rf_rcap_a  = NULL_REG_CAP;
    assign rf_rcap_b  = NULL_REG_CAP;
    assign rf_reg_rdy = {32{1'b1}};

  end else if (RegFile == RegFileLatch) begin : gen_regfile_latch
    ibex_register_file_latch #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (RegFileDataWidth'(prim_secded_pkg::SecdedInv3932ZeroWord))
    ) register_file_i (
      .clk_i (clk),
      .rst_ni(rst_ni),

      .test_en_i       (test_en_i),
      .dummy_instr_id_i(dummy_instr_id),

      .raddr_a_i(rf_raddr_a),
      .rdata_a_o(rf_rdata_a_ecc),
      .raddr_b_i(rf_raddr_b),
      .rdata_b_o(rf_rdata_b_ecc),
      .waddr_a_i(rf_waddr_wb),
      .wdata_a_i(rf_wdata_wb_ecc),
      .we_a_i   (rf_we_wb)
    );

    assign rf_rcap_a  = NULL_REG_CAP;
    assign rf_rcap_b  = NULL_REG_CAP;
    assign rf_reg_rdy = {32{1'b1}};

  end

  ///////////////////////////////
  // Scrambling Infrastructure //
  ///////////////////////////////

  if (ICacheScramble) begin : gen_scramble

  // Scramble key valid starts with OTP returning new valid key and stays high
  // until we request a new valid key.
    assign scramble_key_valid_d = scramble_req_q ? scramble_key_valid_i :
                                  icache_inval   ? 1'b0                 :
                                                   scramble_key_valid_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        scramble_key_q       <= RndCnstIbexKey;
        scramble_nonce_q     <= RndCnstIbexNonce;
      end else if (scramble_key_valid_i) begin
        scramble_key_q       <= scramble_key_i;
        scramble_nonce_q     <= scramble_nonce_i;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        scramble_key_valid_q <= 1'b1;
        scramble_req_q       <= '0;
      end else begin
        scramble_key_valid_q <= scramble_key_valid_d;
        scramble_req_q       <= scramble_req_d;
      end
    end

  // Scramble key request starts with invalidate signal from ICache and stays high
  // until we got a valid key.
    assign scramble_req_d = scramble_req_q ? ~scramble_key_valid_i : icache_inval;
    assign scramble_req_o = scramble_req_q;

  end else begin : gen_noscramble

    logic unused_scramble_inputs = scramble_key_valid_i & (|scramble_key_i) & (|RndCnstIbexKey) &
                                   (|scramble_nonce_i) & (|RndCnstIbexNonce) & scramble_req_q &
                                   icache_inval & scramble_key_valid_d & scramble_req_d;

    assign scramble_req_d       = 1'b0;
    assign scramble_req_q       = 1'b0;
    assign scramble_req_o       = 1'b0;
    assign scramble_key_q       = '0;
    assign scramble_nonce_q     = '0;
    assign scramble_key_valid_q = 1'b1;
    assign scramble_key_valid_d = 1'b1;
  end

  ////////////////////////
  // Rams Instantiation //
  ////////////////////////

  if (ICache) begin : gen_rams

    for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams_inner

      // Tag RAM instantiation
      prim_ram_1p_scr #(
        .Width            (TagSizeECC),
        .Depth            (IC_NUM_LINES),
        .DataBitsPerMask  (TagSizeECC),
        .EnableParity     (0),
        .DiffWidth        (TagSizeECC),
        .NumAddrScrRounds (NumAddrScrRounds),
        .NumDiffRounds    (NumDiffRounds)
      ) tag_bank (
        .clk_i,
        .rst_ni,

        .key_valid_i (scramble_key_valid_q),
        .key_i       (scramble_key_q),
        .nonce_i     (scramble_nonce_q),

        .req_i       (ic_tag_req[way]),

        .gnt_o       (),
        .write_i     (ic_tag_write),
        .addr_i      (ic_tag_addr),
        .wdata_i     (ic_tag_wdata),
        .wmask_i     ({TagSizeECC{1'b1}}),
        .intg_error_i(1'b0),

        .rdata_o     (ic_tag_rdata[way]),
        .rvalid_o    (),
        .raddr_o     (),
        .rerror_o    (),
        .cfg_i       (ram_cfg_i)
      );

      // Data RAM instantiation
      prim_ram_1p_scr #(
        .Width              (LineSizeECC),
        .Depth              (IC_NUM_LINES),
        .DataBitsPerMask    (LineSizeECC),
        .ReplicateKeyStream (1),
        .EnableParity       (0),
        .DiffWidth          (LineSizeECC),
        .NumAddrScrRounds   (NumAddrScrRounds),
        .NumDiffRounds      (NumDiffRounds)
      ) data_bank (
        .clk_i,
        .rst_ni,

        .key_valid_i (scramble_key_valid_q),
        .key_i       (scramble_key_q),
        .nonce_i     (scramble_nonce_q),

        .req_i       (ic_data_req[way]),

        .gnt_o       (),
        .write_i     (ic_data_write),
        .addr_i      (ic_data_addr),
        .wdata_i     (ic_data_wdata),
        .wmask_i     ({LineSizeECC{1'b1}}),
        .intg_error_i(1'b0),

        .rdata_o     (ic_data_rdata[way]),
        .rvalid_o    (),
        .raddr_o     (),
        .rerror_o    (),
        .cfg_i       (ram_cfg_i)
      );
    end

  end else begin : gen_norams

    prim_ram_1p_pkg::ram_1p_cfg_t unused_ram_cfg;
    logic unused_ram_inputs;

    assign unused_ram_cfg    = ram_cfg_i;
    assign unused_ram_inputs = (|ic_tag_req) & ic_tag_write & (|ic_tag_addr) & (|ic_tag_wdata) &
                               (|ic_data_req) & ic_data_write & (|ic_data_addr) & (|ic_data_wdata) &
                               (|scramble_key_q) & (|scramble_nonce_q) & scramble_key_valid_q &
                               scramble_key_valid_d & (|scramble_nonce_q) &
                               (|NumAddrScrRounds);

    assign ic_tag_rdata      = '{default:'b0};
    assign ic_data_rdata     = '{default:'b0};

  end

  // Redundant lockstep core implementation
  if (Lockstep) begin : gen_lockstep
    // Note: certain synthesis tools like DC are very smart at optimizing away redundant logic.
    // Hence, we have to insert an optimization barrier at the IOs of the lockstep Ibex.
    // This is achieved by manually buffering each bit using prim_buf.
    // Our Xilinx and DC synthesis flows make sure that these buffers cannot be optimized away
    // using keep attributes (Vivado) and size_only constraints (DC).
    logic [37:0] rf_wcap_vec, rf_rcap_a_vec, rf_rcap_b_vec;

    localparam int NumBufferBits = $bits({
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_rdata_intg_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_is_cap_o,
      data_rdata_i,
      data_rdata_intg_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      scramble_key_valid_i,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      double_fault_seen_o,
      fetch_enable_i,
      icache_inval,
      core_busy_d,
      cheri_pmode_i,
      cheri_tsafe_en_i,
      rf_wcap_vec,
      rf_rcap_a_vec,
      rf_rcap_b_vec,
      rf_reg_rdy,
      rf_trsv_en,
      rf_trsv_addr,
      rf_trsv_par,
      rf_trvk_addr,
      rf_trvk_en,
      rf_trvk_clrtag,
      rf_trvk_par,
      tsmap_cs_o,
      tsmap_addr_o,
      tsmap_rdata_i,
      tsmap_rdata_intg_i,
      mmreg_corein_i,
      mmreg_coreout_o
    });

    logic [NumBufferBits-1:0] buf_in, buf_out;

    logic [31:0]                  hart_id_local;
    logic [31:0]                  boot_addr_local;

    logic                         instr_req_local;
    logic                         instr_gnt_local;
    logic                         instr_rvalid_local;
    logic [31:0]                  instr_addr_local;
    logic [31:0]                  instr_rdata_local;
    logic [6:0]                   instr_rdata_intg_local;
    logic                         instr_err_local;

    logic                         data_req_local;
    logic                         data_gnt_local;
    logic                         data_rvalid_local;
    logic                         data_we_local;
    logic [3:0]                   data_be_local;
    logic [31:0]                  data_addr_local;
    logic [DataWidth-1:0]         data_wdata_local;
    logic                         data_is_cap_local;
    logic [6:0]                   data_wdata_intg_local;
    logic [DataWidth-1:0]         data_rdata_local;
    logic [6:0]                   data_rdata_intg_local;
    logic                         data_err_local;

    logic                         dummy_instr_id_local;
    logic [4:0]                   rf_raddr_a_local;
    logic [4:0]                   rf_raddr_b_local;
    logic [4:0]                   rf_waddr_wb_local;
    logic                         rf_we_wb_local;
    logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_local;

    logic                         cheri_pmode_local;
    logic                         cheri_tsafe_en_local;
    logic [37:0]                  rf_wcap_vec_local;
    logic [37:0]                  rf_rcap_a_vec_local; 
    logic [37:0]                  rf_rcap_b_vec_local;
    logic [31:0]                  rf_reg_rdy_local;
    logic                         rf_trsv_en_local;
    logic [4:0]                   rf_trsv_addr_local;
    logic [6:0]                   rf_trsv_par_local;
    logic [4:0]                   rf_trvk_addr_local;
    logic                         rf_trvk_en_local;
    logic                         rf_trvk_clrtag_local;
    logic [6:0]                   rf_trvk_par_local;
    logic                         tsmap_cs_local;
    logic [15:0]                  tsmap_addr_local;
    logic [31:0]                  tsmap_rdata_local;
    logic [6:0]                   tsmap_rdata_intg_local;
    logic [MMRegDinW-1:0]         mmreg_corein_local;
    logic [MMRegDoutW-1:0]        mmreg_coreout_local;
    reg_cap_t                     rf_wcap_local, rf_rcap_a_local, rf_rcap_b_local;

    logic [IC_NUM_WAYS-1:0]       ic_tag_req_local;
    logic                         ic_tag_write_local;
    logic [IC_INDEX_W-1:0]        ic_tag_addr_local;
    logic [TagSizeECC-1:0]        ic_tag_wdata_local;
    logic [IC_NUM_WAYS-1:0]       ic_data_req_local;
    logic                         ic_data_write_local;
    logic [IC_INDEX_W-1:0]        ic_data_addr_local;
    logic [LineSizeECC-1:0]       ic_data_wdata_local;
    logic                         scramble_key_valid_local;

    logic                         irq_software_local;
    logic                         irq_timer_local;
    logic                         irq_external_local;
    logic [14:0]                  irq_fast_local;
    logic                         irq_nm_local;
    logic                         irq_pending_local;

    logic                         debug_req_local;
    crash_dump_t                  crash_dump_local;
    logic                         double_fault_seen_local;
    fetch_enable_t                fetch_enable_local;

    logic                         icache_inval_local;
    logic                         core_busy_local;

    assign buf_in = {
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_rdata_intg_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_is_cap_o,
      data_rdata_i,
      data_rdata_intg_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      scramble_key_valid_q,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      double_fault_seen_o,
      fetch_enable_i,
      icache_inval,
      core_busy_d,
      cheri_pmode_i,
      cheri_tsafe_en_i,
      rf_wcap_vec,
      rf_rcap_a_vec,
      rf_rcap_b_vec,
      rf_reg_rdy,
      rf_trsv_en,
      rf_trsv_addr,
      rf_trsv_par,
      rf_trvk_addr,
      rf_trvk_en,
      rf_trvk_clrtag,
      rf_trvk_par,
      tsmap_cs_o,
      tsmap_addr_o,
      tsmap_rdata_i,
      tsmap_rdata_intg_i,
      mmreg_corein_i,
      mmreg_coreout_o
    };

    assign {
      hart_id_local,
      boot_addr_local,
      instr_req_local,
      instr_gnt_local,
      instr_rvalid_local,
      instr_addr_local,
      instr_rdata_local,
      instr_rdata_intg_local,
      instr_err_local,
      data_req_local,
      data_gnt_local,
      data_rvalid_local,
      data_we_local,
      data_be_local,
      data_addr_local,
      data_wdata_local,
      data_is_cap_local,
      data_rdata_local,
      data_rdata_intg_local,
      data_err_local,
      dummy_instr_id_local,
      rf_raddr_a_local,
      rf_raddr_b_local,
      rf_waddr_wb_local,
      rf_we_wb_local,
      rf_wdata_wb_ecc_local,
      rf_rdata_a_ecc_local,
      rf_rdata_b_ecc_local,
      ic_tag_req_local,
      ic_tag_write_local,
      ic_tag_addr_local,
      ic_tag_wdata_local,
      ic_data_req_local,
      ic_data_write_local,
      ic_data_addr_local,
      ic_data_wdata_local,
      scramble_key_valid_local,
      irq_software_local,
      irq_timer_local,
      irq_external_local,
      irq_fast_local,
      irq_nm_local,
      irq_pending_local,
      debug_req_local,
      crash_dump_local,
      double_fault_seen_local,
      fetch_enable_local,
      icache_inval_local,
      core_busy_local,
      cheri_pmode_local,
      cheri_tsafe_en_local,
      rf_wcap_vec_local,
      rf_rcap_a_vec_local,
      rf_rcap_b_vec_local,
      rf_reg_rdy_local,
      rf_trsv_en_local,
      rf_trsv_addr_local,
      rf_trsv_par_local,
      rf_trvk_addr_local,
      rf_trvk_en_local,
      rf_trvk_clrtag_local,
      rf_trvk_par_local,
      tsmap_cs_local,
      tsmap_addr_local,
      tsmap_rdata_local,
      tsmap_rdata_intg_local,
      mmreg_corein_local,
      mmreg_coreout_local
    } = buf_out;

    assign rf_wcap_vec     = reg2vec(rf_wcap);
    assign rf_rcap_a_vec   = reg2vec(rf_rcap_a);
    assign rf_rcap_b_vec   = reg2vec(rf_rcap_b);
    assign rf_wcap_local   = vec2reg(rf_wcap_vec_local);
    assign rf_rcap_a_local = vec2reg(rf_rcap_a_vec_local);
    assign rf_rcap_b_local = vec2reg(rf_rcap_b_vec_local);

    // Manually buffer all input signals.
    prim_buf #(.Width(NumBufferBits)) u_signals_prim_buf (
      .in_i(buf_in),
      .out_o(buf_out)
    );

    logic [TagSizeECC-1:0]  ic_tag_rdata_local [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] ic_data_rdata_local [IC_NUM_WAYS];
    for (genvar k = 0; k < IC_NUM_WAYS; k++) begin : gen_ways
      prim_buf #(.Width(TagSizeECC)) u_tag_prim_buf (
        .in_i(ic_tag_rdata[k]),
        .out_o(ic_tag_rdata_local[k])
      );
      prim_buf #(.Width(LineSizeECC)) u_data_prim_buf (
        .in_i(ic_data_rdata[k]),
        .out_o(ic_data_rdata_local[k])
      );
    end

    logic lockstep_alert_minor_local, lockstep_alert_major_internal_local;
    logic lockstep_alert_major_bus_local;

    ibex_lockstep #(
      .PMPEnable        (PMPEnable),
      .PMPGranularity   (PMPGranularity),
      .PMPNumRegions    (PMPNumRegions),
      .MHPMCounterNum   (MHPMCounterNum),
      .MHPMCounterWidth (MHPMCounterWidth),
      .RV32E            (RV32E),
      .RV32M            (RV32M),
      .RV32B            (RV32B),
      .BranchTargetALU  (BranchTargetALU),
      .ICache           (ICache),
      .ICacheECC        (ICacheECC),
      .BusSizeECC       (BusSizeECC),
      .TagSizeECC       (TagSizeECC),
      .LineSizeECC      (LineSizeECC),
      .BranchPredictor  (BranchPredictor),
      .DbgTriggerEn     (DbgTriggerEn),
      .DbgHwBreakNum    (DbgHwBreakNum),
      .WritebackStage   (WritebackStage),
      .ResetAll         (ResetAll),
      .RndCnstLfsrSeed  (RndCnstLfsrSeed),
      .RndCnstLfsrPerm  (RndCnstLfsrPerm),
      .SecureIbex       (SecureIbex),
      .DummyInstructions(DummyInstructions),
      .RegFileECC       (RegFileECC),
      .RegFileDataWidth (RegFileDataWidth),
      .DmHaltAddr       (DmHaltAddr),
      .DmExceptionAddr  (DmExceptionAddr),
      .CHERIoTEn        (CHERIoTEn),
      .DataWidth        (DataWidth),
      .HeapBase         (HeapBase   ),
      .TSMapBase        (TSMapBase  ),
      .TSMapSize        (TSMapSize),
      .MemCapFmt        (MemCapFmt   ),
      .CheriPPLBC       (CheriPPLBC),
      .CheriSBND2       (CheriSBND2),
      .CheriTBRE        (CheriTBRE)
    ) u_ibex_lockstep (
      .clk_i                  (clk),
      .rst_ni                 (rst_ni),   // should use a different reset tree 

      .hart_id_i              (hart_id_local),
      .boot_addr_i            (boot_addr_local),
      .cheri_pmode_i          (cheri_pmode_local),
      .cheri_tsafe_en_i       (cheri_tsafe_en_local),

      .instr_req_i            (instr_req_local),
      .instr_gnt_i            (instr_gnt_local),
      .instr_rvalid_i         (instr_rvalid_local),
      .instr_addr_i           (instr_addr_local),
      .instr_rdata_i          (instr_rdata_local),
      .instr_rdata_intg_i     (instr_rdata_intg_local),
      .instr_err_i            (instr_err_local),

      .data_req_i             (data_req_local),
      .data_gnt_i             (data_gnt_local),
      .data_rvalid_i          (data_rvalid_local),
      .data_we_i              (data_we_local),
      .data_be_i              (data_be_local),
      .data_addr_i            (data_addr_local),
      .data_wdata_i           (data_wdata_local),
      .data_is_cap_i          (data_is_cap_local),
      .data_wdata_intg_o      (data_wdata_intg_local),
      .data_rdata_i           (data_rdata_local),
      .data_rdata_intg_i      (data_rdata_intg_local),
      .data_err_i             (data_err_local),

      .dummy_instr_id_i       (dummy_instr_id_local),
      .rf_raddr_a_i           (rf_raddr_a_local),
      .rf_raddr_b_i           (rf_raddr_b_local),
      .rf_waddr_wb_i          (rf_waddr_wb_local),
      .rf_we_wb_i             (rf_we_wb_local),
      .rf_wdata_wb_ecc_i      (rf_wdata_wb_ecc_local),
      .rf_rdata_a_ecc_i       (rf_rdata_a_ecc_local),
      .rf_rdata_b_ecc_i       (rf_rdata_b_ecc_local),
      .rf_wcap_wb_i           (rf_wcap_local     ),
      .rf_rcap_a_i            (rf_rcap_a_local      ),
      .rf_rcap_b_i            (rf_rcap_b_local      ),
      .rf_reg_rdy_i           (rf_reg_rdy_local     ),
      .rf_trsv_en_i           (rf_trsv_en_local     ),
      .rf_trsv_addr_i         (rf_trsv_addr_local   ),
      .rf_trsv_par_i          (rf_trsv_par_local ),
      .rf_trvk_addr_i         (rf_trvk_addr_local   ),
      .rf_trvk_en_i           (rf_trvk_en_local     ),
      .rf_trvk_clrtag_i       (rf_trvk_clrtag_local ),
      .rf_trvk_par_i          (rf_trvk_par_local ),
      .tsmap_cs_i             (tsmap_cs_local       ),
      .tsmap_addr_i           (tsmap_addr_local     ),
      .tsmap_rdata_i          (tsmap_rdata_local    ),
      .tsmap_rdata_intg_i     (tsmap_rdata_intg_local),
      .mmreg_corein_i         (mmreg_corein_local  ),
      .mmreg_coreout_i        (mmreg_coreout_local      ), 

      .ic_tag_req_i           (ic_tag_req_local),
      .ic_tag_write_i         (ic_tag_write_local),
      .ic_tag_addr_i          (ic_tag_addr_local),
      .ic_tag_wdata_i         (ic_tag_wdata_local),
      .ic_tag_rdata_i         (ic_tag_rdata_local),
      .ic_data_req_i          (ic_data_req_local),
      .ic_data_write_i        (ic_data_write_local),
      .ic_data_addr_i         (ic_data_addr_local),
      .ic_data_wdata_i        (ic_data_wdata_local),
      .ic_data_rdata_i        (ic_data_rdata_local),
      .ic_scr_key_valid_i     (scramble_key_valid_local),

      .irq_software_i         (irq_software_local),
      .irq_timer_i            (irq_timer_local),
      .irq_external_i         (irq_external_local),
      .irq_fast_i             (irq_fast_local),
      .irq_nm_i               (irq_nm_local),
      .irq_pending_i          (irq_pending_local),

      .debug_req_i            (debug_req_local),
      .crash_dump_i           (crash_dump_local),
      .double_fault_seen_i    (double_fault_seen_local),

      .fetch_enable_i         (fetch_enable_local),
      .alert_minor_o          (lockstep_alert_minor_local),
      .alert_major_internal_o (lockstep_alert_major_internal_local),
      .alert_major_bus_o      (lockstep_alert_major_bus_local),
      .icache_inval_i         (icache_inval_local),
      .core_busy_i            (core_busy_local),
      .test_en_i              (test_en_i),
      .scan_rst_ni            (scan_rst_ni)
    );

    // Manually buffer the output signals.
    prim_buf #(.Width (7)) u_prim_buf_wdata_intg (
      .in_i(data_wdata_intg_local),
      .out_o(data_wdata_intg_o)
    );

    prim_buf u_prim_buf_alert_minor (
      .in_i (lockstep_alert_minor_local),
      .out_o(lockstep_alert_minor)
    );

    prim_buf u_prim_buf_alert_major_internal (
      .in_i (lockstep_alert_major_internal_local),
      .out_o(lockstep_alert_major_internal)
    );

    prim_buf u_prim_buf_alert_major_bus (
      .in_i (lockstep_alert_major_bus_local),
      .out_o(lockstep_alert_major_bus)
    );

  end else begin : gen_no_lockstep
    assign lockstep_alert_major_internal = 1'b0;
    assign lockstep_alert_major_bus      = 1'b0;
    assign lockstep_alert_minor          = 1'b0;
    assign data_wdata_intg_o             = 'b0;
    logic unused_scan, unused_intg;
    assign unused_scan = scan_rst_ni;
    assign unused_intg = |{instr_rdata_intg_i, data_rdata_intg_i};
  end

  assign alert_major_internal_o = core_alert_major | lockstep_alert_major_internal | rf_alert;
  assign alert_major_bus_o      = lockstep_alert_major_bus;
  assign alert_minor_o          = core_alert_minor | lockstep_alert_minor;

endmodule
