// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// 
// Interface to LSU, handles earlyLoad and CHERIoT checking
//
module lsu_if import super_pkg::*; import cheri_pkg::*; # (
  parameter bit CHERIoTEn = 1'b1, 
  parameter bit EarlyLoad = 1'b1 
) (
  input  logic          clk_i,
  input  logic          rst_ni,
  
  input  logic          cheri_pmode_i,

  input  logic          flush_i,
  input  logic          us_valid_i,
  input  lsu_req_info_t lsu_req_dec_i,
  output logic          lsif_rdy_o,

  input  logic          lsu_req_done_i,
  output logic          lsu_req_o,
  output lsu_req_info_t lsu_req_info_o
  );

  typedef enum logic [2:0] {
    IDLE      = 3'h0,
    DLY0_WGNT = 3'h1,
    DLY1      = 3'h2,
    DLY1_WGNT = 3'h3
  } lsif_fsm_e;

  lsif_fsm_e     lsif_fsm_d, lsif_fsm_q;
  lsu_req_info_t req_dly_q, req_hold_q, req_dly_tmp;
  logic          lsif_rdy_local;
  logic          valid_new_req, req_dly_valid;
  logic          is_early_load;
  logic          xfr2hold0, xfr2hold1;
  logic          cheri_pmode;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  assign lsif_rdy_o     = lsif_rdy_local;
  assign lsif_rdy_local = (lsif_fsm_q == IDLE) || (lsif_fsm_q == DLY1);

  // req only considered valid if not otherwise blocked
  assign valid_new_req = us_valid_i & lsif_rdy_o;
  assign is_early_load = us_valid_i & lsu_req_dec_i.early_load;

  if (CHERIoTEn) begin : gen_req_check
    logic [7:0] cheri_check_result;
    always_comb begin
      cheri_check_result = ~cheri_pmode ? 7'h0 : 
                           cheri_ls_check (req_dly_q.lschk_info, req_dly_q.addr,
                                           req_dly_q.rf_we, req_dly_q.is_cap, req_dly_q.data_type);
        
      req_dly_tmp                 = req_dly_q;
      req_dly_tmp.cheri_err       = cheri_check_result[0];
      req_dly_tmp.align_err_only  = cheri_check_result[2];
      req_dly_tmp.cheri_cause     = cheri_check_result[7:3];
      req_dly_tmp.wdata[MEM_TAG] &= ~cheri_check_result[1];    // SLC tag clearing
    end
  end else begin : gen_no_req_check
    assign req_dly_tmp = req_dly_q;
  end

  always_comb begin
    if (lsif_fsm_q == DLY1) begin
      lsu_req_info_o = req_dly_tmp;
    end else if ((lsif_fsm_q == DLY0_WGNT) || (lsif_fsm_q == DLY1_WGNT)) begin
      lsu_req_info_o = req_hold_q;
    end else  begin
      lsu_req_info_o = lsu_req_dec_i;
    end
  end

  always_comb begin
    lsif_fsm_d  = lsif_fsm_q;
    lsu_req_o   = 1'b0;
    xfr2hold0   = 1'b0;
    xfr2hold1   = 1'b0;

    case (lsif_fsm_q)
      IDLE: begin
        if (valid_new_req & is_early_load) begin
          lsu_req_o   = 1'b1;
          if (~lsu_req_done_i) begin
            lsif_fsm_d = DLY0_WGNT;
            xfr2hold0    = 1'b1;   // transfer request from input to hold register
          end
        end else if (valid_new_req) begin
          lsif_fsm_d   = DLY1;
          lsu_req_o   = 1'b0;
        end
      end

      DLY1: begin
        lsu_req_o = req_dly_valid;
        if (flush_i) begin
          lsif_fsm_d = IDLE; 
        end else if (~valid_new_req & (~req_dly_valid | lsu_req_done_i)) begin
          lsif_fsm_d = IDLE;
        end else if (~lsu_req_done_i) begin
          lsif_fsm_d = DLY1_WGNT;
          xfr2hold1  = 1'b1;    // transfer request from DLY register to hold register
        end
      end

      DLY0_WGNT: begin
        lsu_req_o = 1'b1;
        if (flush_i || lsu_req_done_i) 
          lsif_fsm_d = IDLE;
      end

      DLY1_WGNT: begin
        lsu_req_o = 1'b1;
        if (flush_i) 
          lsif_fsm_d = IDLE;
        else if (~valid_new_req & ~req_dly_valid & lsu_req_done_i)
          lsif_fsm_d = IDLE;
        else if (lsu_req_done_i)
          lsif_fsm_d = DLY1;
      end
           
      default: ;
    endcase
   
  end


  // there are 2 buffer stage in lsu_if
  // - req_dly stage addes 1 cycle pipeline delay to non-EarlyLoad requests 
  // - req_hold stage hold requests stable if req_done doesn't come back in the same cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lsif_fsm_q    <= IDLE;
      req_dly_q     <= NULL_LSU_REQ_INFO;
      req_hold_q    <= NULL_LSU_REQ_INFO;
      req_dly_valid <= 1'b0;
    end else  begin
      lsif_fsm_q  <= lsif_fsm_d;

      if (flush_i) begin
        req_dly_valid <= 1'b0;
      end else if (lsif_rdy_local) begin
        req_dly_valid <= valid_new_req;
        req_dly_q     <= lsu_req_dec_i;
      end

      if (xfr2hold0)
        req_hold_q <= lsu_req_dec_i;
      else if (xfr2hold1)
        req_hold_q <= req_dly_tmp;

    end  
  end

`ifdef FORMAL
  AssumeNoFlush: assume property (flush_i == 1'b0);
  AssumeReqDone: assume property (@(posedge clk_i) lsu_req_o |-> ##[0:3] lsu_req_done_i);
  AssertReqProp: assert property (@(posedge clk_i) (us_valid_i & lsif_rdy_o) |-> lsu_req_o);
`endif

endmodule
