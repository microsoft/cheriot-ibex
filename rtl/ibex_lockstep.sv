// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex lockstep module
// This module instantiates a second copy of the core logic, and compares it's outputs against
// those from the main core. The second core runs synchronously with the main core, delayed by
// LockstepOffset cycles.
module ibex_lockstep import ibex_pkg::*; import cheri_pkg::*; #(
  parameter int unsigned LockstepOffset    = 2,
  parameter bit          PMPEnable         = 1'b0,
  parameter int unsigned PMPGranularity    = 0,
  parameter int unsigned PMPNumRegions     = 4,
  parameter int unsigned MHPMCounterNum    = 0,
  parameter int unsigned MHPMCounterWidth  = 40,
  parameter bit          RV32E             = 1'b0,
  parameter rv32m_e      RV32M             = RV32MFast,
  parameter rv32b_e      RV32B             = RV32BNone,
  parameter bit          BranchTargetALU   = 1'b0,
  parameter bit          WritebackStage    = 1'b0,
  parameter bit          ICache            = 1'b0,
  parameter bit          ICacheECC         = 1'b0,
  parameter int unsigned BusSizeECC        = BUS_SIZE,
  parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
  parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
  parameter bit          BranchPredictor   = 1'b0,
  parameter bit          DbgTriggerEn      = 1'b0,
  parameter int unsigned DbgHwBreakNum     = 1,
  parameter bit          ResetAll          = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
  parameter bit          SecureIbex        = 1'b0,
  parameter bit          DummyInstructions = 1'b0,
  parameter bit          RegFileECC        = 1'b0,
  parameter int unsigned RegFileDataWidth  = 32,
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808,
  // CHERIoT paramters
  parameter bit          CHERIoTEn         = 1'b1,
  parameter int unsigned DataWidth         = 33,
  parameter int unsigned HeapBase          ,
  parameter int unsigned TSMapBase         ,
  parameter int unsigned TSMapSize         ,
  parameter bit          MemCapFmt         = 1'b0,
  parameter bit          CheriPPLBC        = 1'b1,
  parameter bit          CheriSBND2        = 1'b0,
  parameter bit          CheriTBRE         = 1'b1,
  parameter int unsigned MMRegDinW         = 128,
  parameter int unsigned MMRegDoutW        = 64
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,
  input  logic                         cheri_pmode_i,
  input  logic                         cheri_tsafe_en_i,
 
  input  logic                         instr_req_i,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  input  logic [31:0]                  instr_addr_i,
  input  logic [31:0]                  instr_rdata_i,
  input  logic [6:0]                   instr_rdata_intg_i,
  input  logic                         instr_err_i,

  input  logic                         data_req_i,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  input  logic                         data_we_i,
  input  logic [3:0]                   data_be_i,
  input  logic [31:0]                  data_addr_i,
  input  logic [DataWidth-1:0]         data_wdata_i,
  input  logic                         data_is_cap_i,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [DataWidth-1:0]         data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  input  logic                         dummy_instr_id_i,
  input  logic [4:0]                   rf_raddr_a_i,
  input  logic [4:0]                   rf_raddr_b_i,
  input  logic [4:0]                   rf_waddr_wb_i,
  input  logic                         rf_we_wb_i,
  input  logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,
 
  input  reg_cap_t                     rf_wcap_wb_i,
  input  reg_cap_t                     rf_rcap_a_i,
  input  reg_cap_t                     rf_rcap_b_i,
  input  logic [31:0]                  rf_reg_rdy_i,
  input  logic                         rf_trsv_en_i,
  input  logic [4:0]                   rf_trsv_addr_i,
  input  logic [6:0]                   rf_trsv_par_i,
  input  logic [4:0]                   rf_trvk_addr_i,
  input  logic                         rf_trvk_en_i,
  input  logic                         rf_trvk_clrtag_i,
  input  logic [6:0]                   rf_trvk_par_i,
  input  logic                         tsmap_cs_i,
  input  logic [15:0]                  tsmap_addr_i,
  input  logic [31:0]                  tsmap_rdata_i,
  input  logic [6:0]                   tsmap_rdata_intg_i,
  input  logic [MMRegDinW-1:0]         mmreg_corein_i,
  input  logic [MMRegDoutW-1:0]        mmreg_coreout_i,
 
  input  logic [IC_NUM_WAYS-1:0]       ic_tag_req_i,
  input  logic                         ic_tag_write_i,
  input  logic [IC_INDEX_W-1:0]        ic_tag_addr_i,
  input  logic [TagSizeECC-1:0]        ic_tag_wdata_i,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  input  logic [IC_NUM_WAYS-1:0]       ic_data_req_i,
  input  logic                         ic_data_write_i,
  input  logic [IC_INDEX_W-1:0]        ic_data_addr_i,
  input  logic [LineSizeECC-1:0]       ic_data_wdata_i,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,

  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,
  input  logic                         irq_pending_i,

  input  logic                         debug_req_i,
  input  crash_dump_t                  crash_dump_i,
  input  logic                         double_fault_seen_i,

  input  fetch_enable_t                fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  input  logic                         icache_inval_i,
  input  logic                         core_busy_i,
  input  logic                         test_en_i,
  input  logic                         scan_rst_ni
);

  localparam int unsigned LockstepOffsetW = $clog2(LockstepOffset);
  // Core outputs are delayed for an extra cycle due to shadow output registers
  localparam int unsigned OutputsOffset = LockstepOffset + 1;

  //////////////////////
  // Reset generation //
  //////////////////////

  // Upon reset, the comparison is stopped and the shadow core is reset, both immediately. A
  // counter is started. After LockstepOffset clock cycles:
  // - The counter is stopped.
  // - The reset of the shadow core is synchronously released.
  // The comparison is started in the following clock cycle.

  logic [LockstepOffsetW-1:0] rst_shadow_cnt_d, rst_shadow_cnt_q, rst_shadow_cnt_incr;
  // Internally generated resets cause IMPERFECTSCH warnings
  /* verilator lint_off IMPERFECTSCH */
  logic                       rst_shadow_set_d, rst_shadow_set_q;
  logic                       rst_shadow_n, enable_cmp_q;
  /* verilator lint_on IMPERFECTSCH */

  assign rst_shadow_cnt_incr = rst_shadow_cnt_q + LockstepOffsetW'(1);

  assign rst_shadow_set_d = (rst_shadow_cnt_q == LockstepOffsetW'(LockstepOffset - 1));
  assign rst_shadow_cnt_d = rst_shadow_set_d ? rst_shadow_cnt_q : rst_shadow_cnt_incr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_shadow_cnt_q <= '0;
      enable_cmp_q     <= '0;
    end else begin
      rst_shadow_cnt_q <= rst_shadow_cnt_d;
      enable_cmp_q     <= rst_shadow_set_q;
    end
  end

  // The primitives below are used to place size-only constraints in order to prevent
  // synthesis optimizations and preserve anchor points for constraining backend tools.
  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_prim_rst_shadow_set_flop (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   (rst_shadow_set_d),
    .q_o   (rst_shadow_set_q)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_rst_shadow_n_mux2 (
    .clk0_i(rst_shadow_set_q),
    .clk1_i(scan_rst_ni),
    .sel_i (test_en_i),
    .clk_o (rst_shadow_n)
  );

  //////////////////
  // Input delays //
  //////////////////

  typedef struct packed {
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [31:0]                 instr_rdata;
    logic                        instr_err;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [DataWidth-1:0]        data_rdata;
    logic                        data_err;
    logic [RegFileDataWidth-1:0] rf_rdata_a_ecc;
    logic [RegFileDataWidth-1:0] rf_rdata_b_ecc;
    logic                        irq_software;
    logic                        irq_timer;
    logic                        irq_external;
    logic [14:0]                 irq_fast;
    logic                        irq_nm;
    logic                        debug_req;
    fetch_enable_t               fetch_enable;
    logic                        ic_scr_key_valid;
    logic                        cheri_pmode;
    logic                        cheri_tsafe_en;
    reg_cap_t                    rf_rcap_a;
    reg_cap_t                    rf_rcap_b;
    logic [31:0]                 rf_reg_rdy;
    logic [31:0]                 tsmap_rdata;
    logic [MMRegDinW-1:0]        mmreg_corein;
  } delayed_inputs_t;

  delayed_inputs_t [LockstepOffset-1:0] shadow_inputs_q;
  delayed_inputs_t                      shadow_inputs_in;
  logic [6:0]                           instr_rdata_intg_q, data_rdata_intg_q;
  logic [6:0]                           tsmap_rdata_intg_q;
  // Packed arrays must be dealt with separately
  logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
  logic [LineSizeECC-1:0]               shadow_data_rdata_q [IC_NUM_WAYS][LockstepOffset];

  // Assign the inputs to the delay structure
  assign shadow_inputs_in.instr_gnt        = instr_gnt_i;
  assign shadow_inputs_in.instr_rvalid     = instr_rvalid_i;
  assign shadow_inputs_in.instr_rdata      = instr_rdata_i;
  assign shadow_inputs_in.instr_err        = instr_err_i;
  assign shadow_inputs_in.data_gnt         = data_gnt_i;
  assign shadow_inputs_in.data_rvalid      = data_rvalid_i;
  assign shadow_inputs_in.data_rdata       = data_rdata_i;
  assign shadow_inputs_in.data_err         = data_err_i;
  assign shadow_inputs_in.rf_rdata_a_ecc   = rf_rdata_a_ecc_i;
  assign shadow_inputs_in.rf_rdata_b_ecc   = rf_rdata_b_ecc_i;
  assign shadow_inputs_in.irq_software     = irq_software_i;
  assign shadow_inputs_in.irq_timer        = irq_timer_i;
  assign shadow_inputs_in.irq_external     = irq_external_i;
  assign shadow_inputs_in.irq_fast         = irq_fast_i;
  assign shadow_inputs_in.irq_nm           = irq_nm_i;
  assign shadow_inputs_in.debug_req        = debug_req_i;
  assign shadow_inputs_in.fetch_enable     = fetch_enable_i;
  assign shadow_inputs_in.ic_scr_key_valid = ic_scr_key_valid_i;
  assign shadow_inputs_in.cheri_pmode      = cheri_pmode_i;
  assign shadow_inputs_in.cheri_tsafe_en   = cheri_tsafe_en_i;
  assign shadow_inputs_in.rf_rcap_a        = rf_rcap_a_i;
  assign shadow_inputs_in.rf_rcap_b        = rf_rcap_b_i;
  assign shadow_inputs_in.rf_reg_rdy       = rf_reg_rdy_i;
  assign shadow_inputs_in.tsmap_rdata      = tsmap_rdata_i;
  assign shadow_inputs_in.mmreg_corein     = mmreg_corein_i;

  // Delay the inputs
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rdata_intg_q <= '0;
      data_rdata_intg_q  <= '0;
      tsmap_rdata_intg_q  <= '0;
      for (int unsigned i = 0; i < LockstepOffset; i++) begin
        shadow_inputs_q[i]     <= delayed_inputs_t'('0);
        shadow_tag_rdata_q[i]  <= '{default: 0};
        shadow_data_rdata_q[i] <= '{default: 0};
      end
    end else begin
      instr_rdata_intg_q <= instr_rdata_intg_i;
      data_rdata_intg_q  <= data_rdata_intg_i;
      tsmap_rdata_intg_q  <= tsmap_rdata_intg_i;
      for (int unsigned i = 0; i < LockstepOffset - 1; i++) begin
        shadow_inputs_q[i]     <= shadow_inputs_q[i+1];
        shadow_tag_rdata_q[i]  <= shadow_tag_rdata_q[i+1];
        shadow_data_rdata_q[i] <= shadow_data_rdata_q[i+1];
      end
      shadow_inputs_q[LockstepOffset-1]     <= shadow_inputs_in;
      shadow_tag_rdata_q[LockstepOffset-1]  <= ic_tag_rdata_i;
      shadow_data_rdata_q[LockstepOffset-1] <= ic_data_rdata_i;
    end
  end

  ////////////////////////////
  // Bus integrity checking //
  ////////////////////////////

  logic        bus_intg_err;
  logic [1:0]  instr_intg_err, data_intg_err, data_intg_err_tmp;
  logic [31:0] unused_wdata;
  logic [1:0]  data_we_q;
  logic [31:0] rdata_tmp;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      data_we_q <= 2'b00;
    end else begin
      if (data_gnt_i) data_we_q[1] <= data_we_i;
      data_we_q[0] <= data_we_q[1];    // align with shadow_inputs_q[LockstepOffset-1]
    end
  end

  // Checks on incoming data
  prim_secded_inv_39_32_dec u_instr_intg_dec (
    .data_i     ({instr_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].instr_rdata}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (instr_intg_err)
  );

  if (CHERIoTEn) begin
    assign rdata_tmp = shadow_inputs_q[LockstepOffset-1].data_rdata[31:0] ^ 
                       {31'h0, shadow_inputs_q[LockstepOffset-1].data_rdata[32]};
  end else begin
    assign rdata_tmp = shadow_inputs_q[LockstepOffset-1].data_rdata[31:0]; 
  end

  prim_secded_inv_39_32_dec u_data_intg_dec (
    .data_i     ({data_rdata_intg_q, rdata_tmp}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (data_intg_err_tmp)
  );

  // only check read data (data_rvalid includes both reads and writes)
  assign data_intg_err = data_we_q[0] ? 2'h0 : data_intg_err_tmp;

  assign bus_intg_err = (shadow_inputs_q[LockstepOffset-1].instr_rvalid & |instr_intg_err) |
                        (shadow_inputs_q[LockstepOffset-1].data_rvalid  & |data_intg_err);

  // Generate integrity bits
  if (CHERIoTEn) begin
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata_i[31:0]^{31'h0, data_wdata_i[32]}),
      .data_o ({data_wdata_intg_o, unused_wdata})
    );
  end else begin
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata_i[31:0]),
      .data_o ({data_wdata_intg_o, unused_wdata})
    );
  end

  
  ////////////////////////////////////////
  // TSMAP interface integrity checking //
  ////////////////////////////////////////

  logic       tsmap_intg_err;
  logic [1:0] tsmap_intg_err_tmp;
  logic [1:0] tsmap_cs_q;

  if (CHERIoTEn && CheriPPLBC) begin
    always @(posedge clk_i, negedge rst_ni) begin
      if (~rst_ni) begin
        tsmap_cs_q <= 2'b00;
      end else begin
        tsmap_cs_q <= {tsmap_cs_i, tsmap_cs_q[1]}; // align with shadow_inputs_q[LockstepOffset-1]
      end
    end

    // Checks on incoming data
    prim_secded_inv_39_32_dec u_tsmap_intg_dec (
      .data_i     ({tsmap_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].tsmap_rdata}),
      .data_o     (),
      .syndrome_o (),
      .err_o      (tsmap_intg_err_tmp)
    );

    assign tsmap_intg_err = tsmap_cs_q[0] & tsmap_intg_err_tmp;

  end else begin
    assign tsmap_intg_err = 1'b0;
  end

  ///////////////////
  // Output delays //
  ///////////////////

  typedef struct packed {
    logic                        instr_req;
    logic [31:0]                 instr_addr;
    logic                        data_req;
    logic                        data_we;
    logic [3:0]                  data_be;
    logic [31:0]                 data_addr;
    logic [DataWidth-1:0]        data_wdata;
    logic                        data_is_cap;
    logic                        dummy_instr_id;
    logic [4:0]                  rf_raddr_a;
    logic [4:0]                  rf_raddr_b;
    logic [4:0]                  rf_waddr_wb;
    logic                        rf_we_wb;
    logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
    logic [IC_NUM_WAYS-1:0]      ic_tag_req;
    logic                        ic_tag_write;
    logic [IC_INDEX_W-1:0]       ic_tag_addr;
    logic [TagSizeECC-1:0]       ic_tag_wdata;
    logic [IC_NUM_WAYS-1:0]      ic_data_req;
    logic                        ic_data_write;
    logic [IC_INDEX_W-1:0]       ic_data_addr;
    logic [LineSizeECC-1:0]      ic_data_wdata;
    logic                        irq_pending;
    crash_dump_t                 crash_dump;
    logic                        double_fault_seen;
    logic                        icache_inval;
    logic                        core_busy;
    reg_cap_t                    rf_wcap_wb;
    logic                        rf_trsv_en;
    logic [4:0]                  rf_trsv_addr;
    logic [6:0]                  rf_trsv_par;
    logic [4:0]                  rf_trvk_addr;
    logic                        rf_trvk_en;
    logic                        rf_trvk_clrtag;
    logic [6:0]                  rf_trvk_par;
    logic                        tsmap_cs;
    logic [15:0]                 tsmap_addr;
    logic [MMRegDoutW-1:0]       mmreg_coreout;
  } delayed_outputs_t;

  delayed_outputs_t [OutputsOffset-1:0]  core_outputs_q;
  delayed_outputs_t                      core_outputs_in;
  delayed_outputs_t                      shadow_outputs_d, shadow_outputs_q;

  // Assign core outputs to the structure
  assign core_outputs_in.instr_req           = instr_req_i;
  assign core_outputs_in.instr_addr          = instr_addr_i;
  assign core_outputs_in.data_req            = data_req_i;
  assign core_outputs_in.data_we             = data_we_i;
  assign core_outputs_in.data_be             = data_be_i;
  assign core_outputs_in.data_addr           = data_addr_i;
  assign core_outputs_in.data_wdata          = data_wdata_i;
  assign core_outputs_in.data_is_cap         = data_is_cap_i;
  assign core_outputs_in.dummy_instr_id      = dummy_instr_id_i;
  assign core_outputs_in.rf_raddr_a          = rf_raddr_a_i;
  assign core_outputs_in.rf_raddr_b          = rf_raddr_b_i;
  assign core_outputs_in.rf_waddr_wb         = rf_waddr_wb_i;
  assign core_outputs_in.rf_we_wb            = rf_we_wb_i;
  assign core_outputs_in.rf_wdata_wb_ecc     = rf_wdata_wb_ecc_i;
  assign core_outputs_in.ic_tag_req          = ic_tag_req_i;
  assign core_outputs_in.ic_tag_write        = ic_tag_write_i;
  assign core_outputs_in.ic_tag_addr         = ic_tag_addr_i;
  assign core_outputs_in.ic_tag_wdata        = ic_tag_wdata_i;
  assign core_outputs_in.ic_data_req         = ic_data_req_i;
  assign core_outputs_in.ic_data_write       = ic_data_write_i;
  assign core_outputs_in.ic_data_addr        = ic_data_addr_i;
  assign core_outputs_in.ic_data_wdata       = ic_data_wdata_i;
  assign core_outputs_in.irq_pending         = irq_pending_i;
  assign core_outputs_in.crash_dump          = crash_dump_i;
  assign core_outputs_in.double_fault_seen   = double_fault_seen_i;
  assign core_outputs_in.icache_inval        = icache_inval_i;
  assign core_outputs_in.core_busy           = core_busy_i;
  assign core_outputs_in.rf_wcap_wb          = rf_wcap_wb_i;
  assign core_outputs_in.rf_trsv_en          = rf_trsv_en_i;
  assign core_outputs_in.rf_trsv_addr        = rf_trsv_addr_i;
  assign core_outputs_in.rf_trsv_par         = rf_trsv_par_i;
  assign core_outputs_in.rf_trvk_addr        = rf_trvk_addr_i;
  assign core_outputs_in.rf_trvk_en          = rf_trvk_en_i;
  assign core_outputs_in.rf_trvk_clrtag      = rf_trvk_clrtag_i;
  assign core_outputs_in.rf_trvk_par         = rf_trvk_par_i;
  assign core_outputs_in.tsmap_cs            = tsmap_cs_i;
  assign core_outputs_in.tsmap_addr          = tsmap_addr_i;
  assign core_outputs_in.mmreg_coreout       = mmreg_coreout_i;     
                        
  // Delay the outputs
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < OutputsOffset - 1; i++) begin
      core_outputs_q[i] <= core_outputs_q[i+1];
    end
    core_outputs_q[OutputsOffset-1] <= core_outputs_in;
  end

  ///////////////////////////////
  // Shadow core instantiation //
  ///////////////////////////////

  logic shadow_alert_minor, shadow_alert_major;

  ibex_core #(
    .PMPEnable         ( PMPEnable         ),
    .PMPGranularity    ( PMPGranularity    ),
    .PMPNumRegions     ( PMPNumRegions     ),
    .MHPMCounterNum    ( MHPMCounterNum    ),
    .MHPMCounterWidth  ( MHPMCounterWidth  ),
    .RV32E             ( RV32E             ),
    .RV32M             ( RV32M             ),
    .RV32B             ( RV32B             ),
    .BranchTargetALU   ( BranchTargetALU   ),
    .ICache            ( ICache            ),
    .ICacheECC         ( ICacheECC         ),
    .BusSizeECC        ( BusSizeECC        ),
    .TagSizeECC        ( TagSizeECC        ),
    .LineSizeECC       ( LineSizeECC       ),
    .BranchPredictor   ( BranchPredictor   ),
    .DbgTriggerEn      ( DbgTriggerEn      ),
    .DbgHwBreakNum     ( DbgHwBreakNum     ),
    .WritebackStage    ( WritebackStage    ),
    .ResetAll          ( ResetAll          ),
    .RndCnstLfsrSeed   ( RndCnstLfsrSeed   ),
    .RndCnstLfsrPerm   ( RndCnstLfsrPerm   ),
    .SecureIbex        ( SecureIbex        ),
    .DummyInstructions ( DummyInstructions ),
    .RegFileECC        ( RegFileECC        ),
    .RegFileDataWidth  ( RegFileDataWidth  ),
    .DmHaltAddr        ( DmHaltAddr        ),
    .DmExceptionAddr   ( DmExceptionAddr   ),
    .CHERIoTEn         ( CHERIoTEn),
    .DataWidth         ( DataWidth),
    .HeapBase          ( HeapBase   ),
    .TSMapBase         ( TSMapBase  ),
    .TSMapSize         ( TSMapSize),
    .MemCapFmt         ( MemCapFmt   ),
    .CheriPPLBC        ( CheriPPLBC),
    .CheriSBND2        ( CheriSBND2),
    .CheriTBRE         ( CheriTBRE)
  ) u_shadow_core (
    .clk_i               (clk_i),
    .rst_ni              (rst_shadow_n),

    .hart_id_i           (hart_id_i),
    .boot_addr_i         (boot_addr_i),

    .cheri_pmode_i       (shadow_inputs_q[0].cheri_pmode),
    .cheri_tsafe_en_i    (shadow_inputs_q[0].cheri_tsafe_en),

    .instr_req_o         (shadow_outputs_d.instr_req),
    .instr_gnt_i         (shadow_inputs_q[0].instr_gnt),
    .instr_rvalid_i      (shadow_inputs_q[0].instr_rvalid),
    .instr_addr_o        (shadow_outputs_d.instr_addr),
    .instr_rdata_i       (shadow_inputs_q[0].instr_rdata),
    .instr_err_i         (shadow_inputs_q[0].instr_err),

    .data_req_o          (shadow_outputs_d.data_req),
    .data_gnt_i          (shadow_inputs_q[0].data_gnt),
    .data_rvalid_i       (shadow_inputs_q[0].data_rvalid),
    .data_we_o           (shadow_outputs_d.data_we),
    .data_be_o           (shadow_outputs_d.data_be),
    .data_addr_o         (shadow_outputs_d.data_addr),
    .data_wdata_o        (shadow_outputs_d.data_wdata),
    .data_is_cap_o       (shadow_outputs_d.data_is_cap),
    .data_rdata_i        (shadow_inputs_q[0].data_rdata),
    .data_err_i          (shadow_inputs_q[0].data_err),

    .dummy_instr_id_o    (shadow_outputs_d.dummy_instr_id),
    .rf_raddr_a_o        (shadow_outputs_d.rf_raddr_a),
    .rf_raddr_b_o        (shadow_outputs_d.rf_raddr_b),
    .rf_waddr_wb_o       (shadow_outputs_d.rf_waddr_wb),
    .rf_we_wb_o          (shadow_outputs_d.rf_we_wb),
    .rf_wdata_wb_ecc_o   (shadow_outputs_d.rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i    (shadow_inputs_q[0].rf_rdata_a_ecc),
    .rf_rdata_b_ecc_i    (shadow_inputs_q[0].rf_rdata_b_ecc),
    .rf_wcap_wb_o        (shadow_outputs_d.rf_wcap_wb),
    .rf_rcap_a_i         (shadow_inputs_q[0].rf_rcap_a),
    .rf_rcap_b_i         (shadow_inputs_q[0].rf_rcap_b),
    .rf_reg_rdy_i        (shadow_inputs_q[0].rf_reg_rdy),
    .rf_trsv_en_o        (shadow_outputs_d.rf_trsv_en),  
    .rf_trsv_addr_o      (shadow_outputs_d.rf_trsv_addr),
    .rf_trsv_par_o       (shadow_outputs_d.rf_trsv_par),
    .rf_trvk_addr_o      (shadow_outputs_d.rf_trvk_addr),
    .rf_trvk_en_o        (shadow_outputs_d.rf_trvk_en),  
    .rf_trvk_clrtag_o    (shadow_outputs_d.rf_trvk_clrtag),
    .rf_trvk_par_o       (shadow_outputs_d.rf_trvk_par),
    .tsmap_cs_o          (shadow_outputs_d.tsmap_cs),    
    .tsmap_addr_o        (shadow_outputs_d.tsmap_addr), 
    .tsmap_rdata_i       (shadow_inputs_q[0].tsmap_rdata),
    .mmreg_corein_i      (shadow_inputs_q[0].mmreg_corein),
    .mmreg_coreout_o     (shadow_outputs_d.mmreg_coreout),  

    .ic_tag_req_o        (shadow_outputs_d.ic_tag_req),
    .ic_tag_write_o      (shadow_outputs_d.ic_tag_write),
    .ic_tag_addr_o       (shadow_outputs_d.ic_tag_addr),
    .ic_tag_wdata_o      (shadow_outputs_d.ic_tag_wdata),
    .ic_tag_rdata_i      (shadow_tag_rdata_q[0]),
    .ic_data_req_o       (shadow_outputs_d.ic_data_req),
    .ic_data_write_o     (shadow_outputs_d.ic_data_write),
    .ic_data_addr_o      (shadow_outputs_d.ic_data_addr),
    .ic_data_wdata_o     (shadow_outputs_d.ic_data_wdata),
    .ic_data_rdata_i     (shadow_data_rdata_q[0]),
    .ic_scr_key_valid_i  (shadow_inputs_q[0].ic_scr_key_valid),

    .irq_software_i      (shadow_inputs_q[0].irq_software),
    .irq_timer_i         (shadow_inputs_q[0].irq_timer),
    .irq_external_i      (shadow_inputs_q[0].irq_external),
    .irq_fast_i          (shadow_inputs_q[0].irq_fast),
    .irq_nm_i            (shadow_inputs_q[0].irq_nm),
    .irq_pending_o       (shadow_outputs_d.irq_pending),

    .debug_req_i         (shadow_inputs_q[0].debug_req),
    .crash_dump_o        (shadow_outputs_d.crash_dump),
    .double_fault_seen_o (shadow_outputs_d.double_fault_seen),

`ifdef RVFI
    .rvfi_valid         (),
    .rvfi_order         (),
    .rvfi_insn          (),
    .rvfi_trap          (),
    .rvfi_halt          (),
    .rvfi_intr          (),
    .rvfi_mode          (),
    .rvfi_ixl           (),
    .rvfi_rs1_addr      (),
    .rvfi_rs2_addr      (),
    .rvfi_rs3_addr      (),
    .rvfi_rs1_rdata     (),
    .rvfi_rs2_rdata     (),
    .rvfi_rs3_rdata     (),
    .rvfi_rd_addr       (),
    .rvfi_rd_wdata      (),
    .rvfi_pc_rdata      (),
    .rvfi_pc_wdata      (),
    .rvfi_mem_addr      (),
    .rvfi_mem_rmask     (),
    .rvfi_mem_wmask     (),
    .rvfi_mem_rdata     (),
    .rvfi_mem_wdata     (),
    .rvfi_ext_mip       (),
    .rvfi_ext_nmi       (),
    .rvfi_ext_debug_req (),
    .rvfi_ext_mcycle    (),
    .rvfi_mem_wcap      (),
    .rvfi_mem_rcap      (),
    .rvfi_mem_is_cap    (),
    .rvfi_rd_wcap       (),
    .rvfi_rs2_rcap      (),
    .rvfi_rs1_rcap      (),
`endif

    .fetch_enable_i    (shadow_inputs_q[0].fetch_enable),
    .alert_minor_o     (shadow_alert_minor),
    .alert_major_o     (shadow_alert_major),
    .icache_inval_o    (shadow_outputs_d.icache_inval),
    .core_busy_o       (shadow_outputs_d.core_busy)
  );

  // Register the shadow core outputs
  always_ff @(posedge clk_i) begin
    shadow_outputs_q <= shadow_outputs_d;
  end

  /////////////////////////
  // Compare the outputs //
  /////////////////////////

  logic outputs_mismatch;

  assign outputs_mismatch       = enable_cmp_q & (shadow_outputs_q != core_outputs_q[0]);
  assign alert_major_internal_o = outputs_mismatch | shadow_alert_major;
  assign alert_major_bus_o      = bus_intg_err | tsmap_intg_err;
  assign alert_minor_o          = shadow_alert_minor;

endmodule
