// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Instruction Fetch Stage
 *
 * Instruction fetch unit: Selection of the next PC, and buffering (sampling) of
 * the read instruction.
 */

module if_stage import super_pkg::*; #(
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808,
  parameter bit          BranchPredictor   = 1'b0,
  parameter bit          CHERIoTEn         = 1'b0,
  parameter bit          InstrBufEn        = 1'b1,
  parameter bit          CompDecEn         = 1'b1,
  parameter bit          UnalignedFetch    = 1'b1
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        cheri_pmode_i,
  input  logic                        req_i,                    // instruction request control
  input  logic                        debug_mode_i,

  input  logic [31:0]                 boot_addr_i,

  // instruction cache interface
  output logic                        instr_req_o,
  output logic [31:0]                 instr_addr_o,
  input  logic                        instr_gnt_i,
  input  logic                        instr_rvalid_i,
  input  logic [63:0]                 instr_rdata_i,
  input  logic                        instr_err_i,

  // output of ID stage
  input  logic [1:0]                  ds_rdy_i,
  output ir_reg_t                     if_instr0_o,
  output ir_reg_t                     if_instr1_o,
  output logic [1:0]                  if_valid_o,

  // control signals
  input  logic                        ex_pc_set_i,              // set the PC to a new value
  input  logic [31:0]                 ex_pc_target_i,           // Not-taken branch address in ID/EX
                                                                // vectorized interrupt lines
  input  logic                        ex_bp_init_i, 
  input  ex_bp_info_t                 ex_bp_info_i, 

  // misc signals
  output logic                        if_busy_o                 // IF stage is busy fetching instr
);

  // prefetch buffer related signals
  logic         prefetch_busy;
  logic         branch_req;
  logic  [31:0] fetch_addr_n;

  logic         predict_pc_set;
  logic  [31:0] predict_pc_target;
  logic  [1:0]  fetch_valid;

  ir_reg_t      fetch_instr0, fetch_instr1;
  ir_reg_t      pdt_instr0, pdt_instr1;

  logic  [31:0] instr1_pc_spec0;
  logic  [31:0] instr1_pc_spec1;

  // The Branch predictor can provide a new PC which is internal to if_stage. Only override the mux
  // select to choose this if the core isn't already trying to set a PC.
  assign fetch_addr_n = ex_pc_set_i ? ex_pc_target_i : predict_pc_target;
  
  prefetch_buffer64 #(.UnalignedFetch (UnalignedFetch)) prefetch_buffer_i (
      .clk_i               ( clk_i                      ),
      .rst_ni              ( rst_ni                     ),
      .req_i               ( req_i                      ),
      .branch_i            ( branch_req                 ),
      .addr_i              ( {fetch_addr_n[31:1], 1'b0} ),
      .ready_i             ( ds_rdy_i                   ),
      .valid_o             ( fetch_valid                ),
      .instr0_o            ( fetch_instr0               ),
      .instr1_o            ( fetch_instr1               ),
      .instr1_pc_spec0_o   ( instr1_pc_spec0            ),
      .instr1_pc_spec1_o   ( instr1_pc_spec1            ),
      .instr_req_o         ( instr_req_o                ),
      .instr_addr_o        ( instr_addr_o               ),
      .instr_gnt_i         ( instr_gnt_i                ),
      .instr_rvalid_i      ( instr_rvalid_i             ),
      .instr_rdata_i       ( instr_rdata_i              ),
      .instr_err_i         ( instr_err_i                ),
      .busy_o              ( prefetch_busy              )
  );

  assign branch_req  = ex_pc_set_i | predict_pc_set;
  assign if_busy_o   = prefetch_busy;

  branch_predict #(.InstrBufEn (InstrBufEn)) branch_predict_i (
    .clk_i               (clk_i            ),
    .rst_ni              (rst_ni           ),
    .pdt_en_i            (1'b1             ),
    .tbl_rst_val_i       (boot_addr_i      ),
    .ex_bp_init_i        (ex_bp_init_i     ), 
    .ex_bp_info_i        (ex_bp_info_i     ), 
    .instr_gnt_i         (instr_gnt_i      ),
    .predict_pc_set_o    (predict_pc_set   ),
    .predict_pc_target_o (predict_pc_target),
    .fetch_valid_i       (fetch_valid      ),
    .fetch_instr0_i      (fetch_instr0     ), 
    .fetch_instr1_i      (fetch_instr1     ), 
    .instr1_pc_spec0_i   (instr1_pc_spec0  ),
    .instr1_pc_spec1_i   (instr1_pc_spec1  ),
    .ds_rdy_i            (ds_rdy_i         ),
    .pdt_valid_o         (if_valid_o       ),
    .pdt_instr0_o        (pdt_instr0       ), 
    .pdt_instr1_o        (pdt_instr1       )
  );

  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  if (CompDecEn) begin : gen_compressed_decoder
    compressed_decoder #(
      .CHERIoTEn (CHERIoTEn)
    ) compressed_decoder_0 (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .cheri_pmode_i  (cheri_pmode_i),
      .instr_i        (pdt_instr0),
      .instr_o        (if_instr0_o)
    );

    compressed_decoder #(
      .CHERIoTEn (CHERIoTEn)
    ) compressed_decoder_1 (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .cheri_pmode_i  (cheri_pmode_i),
      .instr_i        (pdt_instr1),
      .instr_o        (if_instr1_o)
    );
  end else begin : gen_no_compressed_decoder
    assign if_instr0_o = pdt_instr0;
    assign if_instr1_o = pdt_instr1;
  end

  //end
endmodule
