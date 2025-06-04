// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Instruction Commit logic
//

module committer import super_pkg::*; # (
  parameter bit          CHERIoTEn  = 1'b0
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  // Commit FIFO interface
  input  logic [1:0]        sbdfifo_rd_valid_i,
  input  sbd_fifo_t         sbdfifo_rdata0_i,
  input  sbd_fifo_t         sbdfifo_rdata1_i,
  output logic [1:0]        sbdfifo_rd_rdy_o,
  
  // EX pipeline interface
  input  logic              alupl0_valid_i,
  input  pl_out_t           alupl0_output_i,
  output logic              alupl0_rdy_o,
  
  input  logic              alupl1_valid_i,
  input  pl_out_t           alupl1_output_i,
  output logic              alupl1_rdy_o,

  input  logic              lspl_valid_i,
  input  pl_out_t           lspl_output_i,
  output logic              lspl_rdy_o,

  input  logic              multpl_valid_i,
  input  pl_out_t           multpl_output_i,
  output logic              multpl_rdy_o,

  // isssuer interface
  input  logic              cmt_flush_i,
  output logic [31:0]       cmt_regwr_o,
  output logic              cmt_err_o,
  output cmt_err_info_t     cmt_err_info_o,

  // Write ports
  output logic [4:0]        rf_waddr0_o,
  output logic [RegW-1:0]   rf_wdata0_o,
  output logic              rf_we0_o, 

  output logic [4:0]        rf_waddr1_o,
  output logic [RegW-1:0]   rf_wdata1_o,
  output logic              rf_we1_o, 

  output logic [4:0]        rf_waddr2_o,
  output logic [RegW-1:0]   rf_wdata2_o,
  output logic              rf_we2_o      
  );

  logic [4:0]      pl_valid_st, pl_err_st, pl_we_st;
  logic [4:0]      instr0_pl_sel, instr1_pl_sel;
  logic [4:0]      pl_we_vec0, pl_we_vec1;
  logic            cmt_err_q;
  cmt_err_info_t   cmt_err_info_d, cmt_err_info_q;
  logic [31:0]     cmt_err_pc;
                   
  logic            cmt_wrsv0, cmt_wrsv1, cmt_wrsv2;
  logic            load_waddr_conflict, load_early, load_late;
                   
  logic [1:0]      instr_avail, instr_err;
  logic [1:0]      sbd_deq, is_alu_mult;
  logic            sbd_same_pl;

  assign pl_valid_st = {multpl_valid_i, lspl_valid_i, alupl1_valid_i, alupl0_valid_i, 1'b0};
  assign pl_err_st   = {multpl_output_i.err, lspl_output_i.err, alupl1_output_i.err, alupl0_output_i.err, 1'b0};
  assign pl_we_st    = {multpl_output_i.we, lspl_output_i.we, alupl1_output_i.we, alupl0_output_i.we, 1'b0};

  // we have max 2 instructions (instr0/instr1) from the scoreboard FIFO
  // -- basically, follow the sequence:
  //    peek at SBD FIFO, select the PL, if PL output is valid, dequeue both SBD and PL
  // -- The PL for instr1 may become valid before the PL for instr0.
  //    in this case we need to hold off reading from PL for instr1.
  assign instr0_pl_sel  = {5{sbdfifo_rd_valid_i[0]}} & sbdfifo_rdata0_i.pl;
  assign instr_avail[0] = |(instr0_pl_sel & pl_valid_st);
  assign instr_err[0]   = |(instr0_pl_sel & pl_valid_st & pl_err_st);

  assign instr1_pl_sel    = {5{sbdfifo_rd_valid_i[1] & instr_avail[0]}} & sbdfifo_rdata1_i.pl;
  assign instr_avail[1] = |(instr1_pl_sel & pl_valid_st);
  assign instr_err[1]   = |(instr1_pl_sel & pl_valid_st & pl_err_st);

  assign pl_we_vec0 = sbdfifo_rdata0_i.pl & pl_we_st;
  assign pl_we_vec1 = sbdfifo_rdata1_i.pl & pl_we_st;
 
  // if two sbdfifo entries points the same pipeline, we can only read the 1st one
  // -- note JAL/JALR sets both bit 0 and bit1/2
  assign sbd_same_pl    = |(sbdfifo_rdata0_i.pl & sbdfifo_rdata1_i.pl);
  assign is_alu_mult[0] = pl_we_vec0[4] | pl_we_vec0[2] | pl_we_vec0[1];
  assign is_alu_mult[1] = pl_we_vec1[4] | pl_we_vec1[2] | pl_we_vec1[1];

  // dequeuing SBD fifo
  // Read the scoreboard entry and PL even if the instr is erred in the current cycle
  // However stop further reads till flush
  assign sbd_deq[0] = instr_avail[0] & ~cmt_err_q;
   assign sbd_deq[1] = sbd_deq[0] & instr_avail[1] & ~sbd_same_pl;

  assign sbdfifo_rd_rdy_o = sbd_deq;

  // Dequeuing (generate rdy output to) each pipeline
  assign alupl0_rdy_o = (sbd_deq[0] & instr0_pl_sel[1]) | (sbd_deq[1] & instr1_pl_sel[1]);
  assign alupl1_rdy_o = (sbd_deq[0] & instr0_pl_sel[2]) | (sbd_deq[1] & instr1_pl_sel[2]);
  assign lspl_rdy_o   = (sbd_deq[0] & instr0_pl_sel[3]) | (sbd_deq[1] & instr1_pl_sel[3]);
  assign multpl_rdy_o = (sbd_deq[0] & instr0_pl_sel[4]) | (sbd_deq[1] & instr1_pl_sel[4]);

  //   - if an error is detected in the current cycle, we still assert rdy but block rf_we
  assign rf_we0_o = instr_avail[0] & ~(instr_err[0] | cmt_err_q) & is_alu_mult[0];
  assign rf_we1_o = instr_avail[1] & ~(|{instr_err, cmt_err_q}) & ~sbd_same_pl & is_alu_mult[1];

  // muxing RF ports output data/addr
  always_comb begin
    unique case (1'b1)
      pl_we_vec0[1] : begin
        rf_waddr0_o = alupl0_output_i.waddr;
        rf_wdata0_o = alupl0_output_i.wdata;
        cmt_wrsv0   = alupl0_output_i.wrsv;
      end
      pl_we_vec0[2] : begin
        rf_waddr0_o = alupl1_output_i.waddr;
        rf_wdata0_o = alupl1_output_i.wdata;
        cmt_wrsv0   = alupl1_output_i.wrsv;
      end
      pl_we_vec0[4] : begin
        rf_waddr0_o = multpl_output_i.waddr;
        rf_wdata0_o = multpl_output_i.wdata;
        cmt_wrsv0   = multpl_output_i.wrsv;
      end
      default : begin
        rf_waddr0_o = alupl0_output_i.waddr;
        rf_wdata0_o = alupl0_output_i.wdata;
        cmt_wrsv0   = alupl0_output_i.wrsv;
      end
    endcase
   
    unique case (1'b1)
      pl_we_vec1[1] : begin
        rf_waddr1_o = alupl0_output_i.waddr;
        rf_wdata1_o = alupl0_output_i.wdata;
        cmt_wrsv1   = alupl0_output_i.wrsv;
      end
      pl_we_vec1[2] : begin
        rf_waddr1_o = alupl1_output_i.waddr;
        rf_wdata1_o = alupl1_output_i.wdata;
        cmt_wrsv1   = alupl1_output_i.wrsv;
      end
      pl_we_vec1[4] : begin
        rf_waddr1_o = multpl_output_i.waddr;
        rf_wdata1_o = multpl_output_i.wdata;
        cmt_wrsv1   = multpl_output_i.wrsv;
      end
      default : begin
        rf_waddr1_o = alupl0_output_i.waddr;
        rf_wdata1_o = alupl0_output_i.wdata;
        cmt_wrsv1   = alupl0_output_i.wrsv;
      end
    endcase
  end
  
  // LSPL has a dedicated write port to help wdata timing
  // however load/store commit still have to be ordered properly.
  // - rf_wr must be ordered properly (if 2 ports writing to the same address, then the one comes later 
  // - (from cmfifo_rd_rdy[1]) takes effect). This condition is possible since we no longer stall WAW.
  // - we are ok between rf_we0 and rf_we1 since regfile prioritize we2 over we1 over we0
  // - however needs to block rf_we2 (load operation) if it is early.
  assign load_early  = sbdfifo_rd_rdy_o[0] & instr0_pl_sel[3] & pl_we_vec0[3] & 
                        ~instr_err[0] & ~cmt_err_q;
  assign load_late   = sbdfifo_rd_rdy_o[1] & instr1_pl_sel[3] & pl_we_vec1[3] & 
                        ~(|{instr_err, cmt_err_q});

  assign load_waddr_conflict = & load_early & ((rf_we1_o && (rf_waddr2_o == rf_waddr1_o)) ||
                                               (rf_we0_o && (rf_waddr2_o == rf_waddr0_o))) ;

  assign rf_we2_o    = (load_early & ~load_waddr_conflict) | load_late;
  assign rf_waddr2_o = lspl_output_i.waddr;
  assign rf_wdata2_o = lspl_output_i.wdata;
  assign cmt_wrsv2   = lspl_output_i.wrsv;

  // register updated, tell issuer to clear reservation
  assign cmt_regwr_o[0] = 1'b0;

  for (genvar i = 1; i < 32; i++) begin : gen_cmt_reg_wr
    assign cmt_regwr_o[i] = (rf_we0_o & cmt_wrsv0 & (rf_waddr0_o == i)) || 
                            (rf_we1_o & cmt_wrsv1 & (rf_waddr1_o == i)) ||
                            (rf_we2_o & cmt_wrsv2 & (rf_waddr2_o == i)); 
  end

  // register errors from pipelines and report back to issuer

  assign cmt_err_o      = cmt_err_q;
  assign cmt_err_info_o = cmt_err_info_q;

  always_comb begin
    // prioritize instr0 when reporting
    // No error from ALU*PL for now
    cmt_err_info_d = cmt_err_info_q;

    if ((instr0_pl_sel[3] && pl_err_st[3]) || (~instr_err[0] & instr1_pl_sel[3] && pl_err_st[3])) begin
      cmt_err_info_d = '{lspl_output_i.pc, lspl_output_i.mcause, lspl_output_i.mtval};
    end else if ((instr0_pl_sel[4] && pl_err_st[4]) || (~instr_err[0] & instr1_pl_sel[4] && pl_err_st[4])) begin
      cmt_err_info_d = '{multpl_output_i.pc, multpl_output_i.mcause, multpl_output_i.mtval};
    end

  end
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      cmt_err_q      <= 1'b0;
      cmt_err_info_q <= NULL_CMT_ERR_INFO;
    end else begin
      if (cmt_flush_i) 
        cmt_err_q <= 1'b0;
      else if (instr_err[0] | instr_err[1]) 
        cmt_err_q    <= 1'b1;

      cmt_err_info_q <= cmt_err_info_d;
    end
  end

`ifndef SYNTHESIS
  logic [31:0] commit_pc0, commit_pc1;
  assign commit_pc0 = sbdfifo_rd_rdy_o[0] ? sbdfifo_rdata0_i.pc : {32{1'bz}};
  assign commit_pc1 = (sbdfifo_rd_rdy_o[1] & ~instr_err[0]) ? sbdfifo_rdata1_i.pc : {32{1'bz}};

`endif

endmodule 

