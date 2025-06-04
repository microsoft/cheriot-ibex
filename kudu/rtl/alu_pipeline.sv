// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Integer ALU pipeline 
//

module alu_pipeline import super_pkg::*; import cheri_pkg::*; # (
  parameter bit    CHERIoTEn   = 1'b1,
  parameter bit    SingleStage = 1'b1     
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic                 cheri_pmode_i,

  input  logic                 flush_i,

  // upstream (issuer) side interface
  input  logic                 us_valid_i,
  output logic                 alupl_rdy_o,
  input  ir_dec_t              instr_i,
  input  full_data2_t          full_data2_i,
  input  waw_act_t             waw_act_i,

  // CSR interface
  input  pcc_cap_t             pcc_cap_i,
  input  logic                 csr_mstatus_mie_i,

  // data forwarding interface
  output logic [31:0]          fwd_act_o,
  output pl_fwd_t              fwd_info_o,
            
  // downstream (commit) side interface
  input  logic                 ds_rdy_i,
  output logic                 alupl_valid_o,
  output pl_out_t              alupl_output_o
);

  typedef struct packed {
    logic           rf_we;
    logic           is_cheri;
    logic [4:0]     rd;
    logic           cycle2;    // whether instruction only takes 1 cycle (be done in EX1) or 2 cycle (EX2)
    logic [31:0]    pc;
  } alupl_reg_t;

  localparam alupl_reg_t DEF_PL_REG = alupl_reg_t'(0);

  logic ex2_valid, ex2_rdy;
  logic wb_valid, wb_rdy;

  alupl_reg_t   ex2_reg, wb_reg;

  op_a_sel_e    rv32_alu_op_a_mux_sel;    // operand a selection: reg value, PC, immediate or zero
  op_b_sel_e    rv32_alu_op_b_mux_sel;     // operand b selection: reg value or immediate
  alu_op_e      rv32_alu_operator;
  logic [31:0]  rv32_imm;
  logic         instr_2cycle;

  logic         ex2_fwd_valid_d, wb_fwd_valid_d;
  logic         ex2_fwd_valid_q, wb_fwd_valid_q;
  logic         ex2_fwd_ok;
  logic [4:0]   ex2_fwd_rd, wb_fwd_rd;
  logic         ex2_waw_match;
  
  logic           ex1_is_cheri;
  logic [OpW-1:0] ex2_fwd_data, wb_fwd_data;
  logic [31:0]    rv32_alu_result, rv32_alu_result_q;
  logic [OpW-1:0] cheri_alu_result, wb_result;

  logic           cheri_pmode;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  //
  // Data forwarding
  //

  // generate fwd_act_o directly from flops (instead of combinatorially from valid/addr) to help timing 
  assign fwd_act_o[0] = 1'b0;
  for (genvar i = 1; i < 32; i++) begin : gen_fwd_o
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) 
        fwd_act_o[i] <= 1'b0;
      else 
        fwd_act_o[i] <= (ex2_fwd_valid_d && (ex2_fwd_rd == i)) || (wb_fwd_valid_d && (wb_fwd_rd == i));
    end
  end 

  assign fwd_info_o.valid  = {wb_fwd_valid_q, ex2_fwd_valid_q};
  assign fwd_info_o.addr0  = ex2_reg.rd;
  assign fwd_info_o.addr1  = wb_reg.rd;
  assign fwd_info_o.data0  = ex2_fwd_data;
  assign fwd_info_o.data1  = wb_fwd_data;

  // Muxing forwarded data  is done in the issuer

  //
  //  EX1 stage
  // 
  assign alupl_rdy_o = ex2_rdy;

  assign instr_2cycle = 1'b0;    // QQQ

  alu_decoder #(.CHERIoTEn(CHERIoTEn)) alu_decoder_i (
    .instr_i               (instr_i),    
    .cheri_pmode_i         (cheri_pmode),
    .imm_o                 (rv32_imm),
    .alu_operator_o        (rv32_alu_operator),     
    .alu_op_a_mux_sel_o    (rv32_alu_op_a_mux_sel),
    .alu_op_b_mux_sel_o    (rv32_alu_op_b_mux_sel)
  );

  rv32_alu rv32_alu_i (
    .operator_i            (rv32_alu_operator),
    .alu_op_a_mux_sel_i    (rv32_alu_op_a_mux_sel),
    .alu_op_b_mux_sel_i    (rv32_alu_op_b_mux_sel),
    .rf_rdata_a_i          (full_data2_i.d0[31:0]),
    .rf_rdata_b_i          (full_data2_i.d1[31:0]),
    .pc_i                  (instr_i.pc),
    .imm_i                 (rv32_imm),
    .result_o              (rv32_alu_result)
  );

  assign ex1_is_cheri = cheri_pmode & ((|instr_i.cheri_op) | instr_i.is_jal);

  if (CHERIoTEn) begin : gen_cheri_alu

    cheri_alu cheri_alu_i (
      .clk_i              (clk_i),
      .rst_ni             (rst_ni),
      .debug_mode_i       (1'b0),          // QQQ for now
      .alu_en_i           (ex2_rdy),
      .instr_i            (instr_i),
      .full_data2_i       (full_data2_i),
      .rv32_alu_result_i  (rv32_alu_result),
      .pcc_cap_i          (pcc_cap_i),
      .csr_mstatus_mie_i  (csr_mstatus_mie_i),
      .result_ocap_o      (cheri_alu_result)
    );

  end
  
  //
  // EX2 stage
  //

  if (SingleStage) begin : gen_no_ex2_stage
    assign ex2_rdy         = wb_rdy;
    assign ex2_reg         = '{instr_i.rf_we, ex1_is_cheri, instr_i.rd, 1'b0, instr_i.pc}; 
    assign ex2_valid       = us_valid_i;
    assign ex2_waw_match   = 1'b0;
    assign ex2_fwd_ok      = 1'b1;
    assign ex2_fwd_valid_d = 1'b0;
    assign ex2_fwd_valid_q = 1'b0;
    assign ex2_fwd_data    = OpW'(0);
  end else begin : gen_ex2_stage

    assign ex2_rdy = ~ex2_valid | wb_rdy;

    // -- ex2_fwd_ok capatures waw_act event if ex2 is stalled, it is used by WB stage to determine
    //    wheter the instructions result has already been cancelled in EX2 stage
    // -- ex2_fwd_valid_q is the actuall fwd_valid signal.
    // 
    always_comb begin
      if (flush_i) begin
        ex2_fwd_valid_d = 1'b0;
        ex2_fwd_rd      = 0;
      end else if (ex2_rdy) begin
        ex2_fwd_valid_d = us_valid_i & instr_i.rf_we & ~instr_2cycle && (instr_i.rd != 0);
        ex2_fwd_rd      = instr_i.rd;
      end else if (ex2_waw_match) begin
        ex2_fwd_valid_d = 1'b0; 
        ex2_fwd_rd      = ex2_reg.rd;
      end else begin
        ex2_fwd_valid_d = ex2_fwd_valid_q;
        ex2_fwd_rd      = ex2_reg.rd;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) begin
        ex2_valid       <= 1'b0;
        ex2_reg         <= DEF_PL_REG;
        ex2_fwd_valid_q <= 1'b0;
        ex2_fwd_ok      <= 1'b0;
      end else begin
        if (flush_i) begin
          ex2_valid     <= 1'b0;
          ex2_fwd_ok    <= 1'b0;
        end else if (ex2_rdy) begin 
          ex2_valid     <= us_valid_i;
          ex2_reg       <= '{instr_i.rf_we, ex1_is_cheri, instr_i.rd, instr_2cycle, instr_i.pc}; 
          ex2_fwd_ok    <= 1'b1;
        end else if (ex2_waw_match) begin
          ex2_fwd_ok    <= 1'b0;
        end

        ex2_fwd_valid_q <= ex2_fwd_valid_d;
      end
    end

    assign ex2_waw_match = (waw_act_i.valid[0] && (waw_act_i.rd0 == ex2_reg.rd)) || 
                           (waw_act_i.valid[1] && (waw_act_i.rd1 == ex2_reg.rd));
    assign ex2_fwd_data = OpW'(0);          // QQQ

  end

  //
  // WB stage
  //
  logic wb_waw_match;

  assign wb_rdy = ~wb_valid | ds_rdy_i;

  always_comb begin
    if (flush_i) begin
      wb_fwd_valid_d = 1'b0;
      wb_fwd_rd      = 0;
    end else if (wb_rdy) begin
      wb_fwd_valid_d = ex2_valid & ex2_reg.rf_we  && (ex2_reg.rd != 0) & ~ex2_waw_match & ex2_fwd_ok;
      wb_fwd_rd      = ex2_reg.rd;
    end else if (wb_waw_match) begin
      wb_fwd_valid_d = 1'b0;
      wb_fwd_rd      = wb_reg.rd;
    end else begin
      wb_fwd_valid_d = wb_fwd_valid_q;
      wb_fwd_rd      = wb_reg.rd;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      wb_valid       <= 1'b0;
      wb_reg         <= DEF_PL_REG;
      wb_fwd_valid_q <= 1'b0;
      rv32_alu_result_q <= 32'h0;
    end else begin
      if (flush_i) begin
        wb_valid       <= 1'b0;
      end else if (wb_rdy) begin 
        wb_valid       <= ex2_valid;
        wb_reg         <= ex2_reg;
        rv32_alu_result_q <= rv32_alu_result;
      end 

      wb_fwd_valid_q <= wb_fwd_valid_d;
    end
  end

  assign wb_waw_match = (waw_act_i.valid[0] && (waw_act_i.rd0 == wb_reg.rd)) || 
                        (waw_act_i.valid[1] && (waw_act_i.rd1 == wb_reg.rd));

  if (CHERIoTEn) begin
    assign wb_result = wb_reg.is_cheri ? cheri_alu_result : RegW'(rv32_alu_result_q);
  end else begin
    assign wb_result = rv32_alu_result_q;
  end

  assign wb_fwd_data  = wb_result;

  // Output to commit 
  assign alupl_valid_o         = wb_valid;
  assign alupl_output_o.we     = wb_reg.rf_we;
  assign alupl_output_o.wrsv   = wb_reg.rf_we & wb_fwd_valid_q;
  assign alupl_output_o.waddr  = wb_reg.rd;
                               
  assign alupl_output_o.wdata  = wb_result;
  assign alupl_output_o.err    = 1'b0;
  assign alupl_output_o.pc     = wb_reg.pc; 
  assign alupl_output_o.mcause = '0;
  assign alupl_output_o.mtval  = '0;
  assign alupl_output_o.is_cap = '0;          // only used in LS pipeline


endmodule
