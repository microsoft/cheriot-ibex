// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


module cheri_stkz import cheri_pkg::*; (
   // Clock and Reset
  input  logic          clk_i,
  input  logic          rst_ni,

  // CSR register interface
  input  logic          ztop_wr_i,
  input  logic [31:0]   ztop_wdata_i,
  input  full_cap_t     ztop_wfcap_i,
  output logic [31:0]   ztop_rdata_o,
  output reg_cap_t      ztop_rcap_o,
 
  input  logic          unmasked_intr_i,

  output logic          stkz_active_o,
  output logic          stkz_abort_o,
  output logic [31:0]   stkz_ptr_o,
  output logic [31:0]   stkz_base_o,
  output logic          stkz_err_o,

  // LSU req/resp interface (to be multiplixed/qualified)
  input  logic          lsu_stkz_resp_valid_i,
  input  logic          lsu_stkz_resp_err_i,
  input  logic          lsu_stkz_req_done_i,   
  output logic          stkz_lsu_req_o,
  output logic          stkz_lsu_we_o,
  output logic          stkz_lsu_is_cap_o,
  output logic [31:0]   stkz_lsu_addr_o,
  output logic [32:0]   stkz_lsu_wdata_o
);

  typedef enum logic [1:0] {STKZ_IDLE, STKZ_ACTIVE, STKZ_ABORT} stkz_fsm_t;

  stkz_fsm_t  stkz_fsm_d, stkz_fsm_q;

  logic  [29:0] stkz_ptrw, stkz_ptrw_nxt;
  logic  [29:0] stkz_basew;
  logic         stkz_start, stkz_done, stkz_stop, stkz_active;
  reg_cap_t     ztop_rcap, ztop_rcap_nxt;
  logic  [32:0] ztop_wtop33;
  logic  [31:0] ztop_wbase32;
  logic         ptr_le_base, waddr_eq_base;
  logic         cmd_new, cmd_avail, cmd_go, cmd_pending;
  logic         cmd_cap_good;
  logic         cmd_n2z;
  logic         cmd_is_null, cmd_is_null_d, cmd_is_null_q;
  reg_cap_t     cmd_wcap, cmd_wcap_q, cmd_wcap_untagged; 
  logic [31:0]  cmd_wdata, cmd_wdata_q, cmd_wbase32, cmd_wbase32_q;

  assign stkz_lsu_wdata_o  = 33'h0;
  assign stkz_lsu_is_cap_o = 1'b0;        // this means we are really writing 33'h0 to memory
  assign stkz_lsu_we_o     = 1'b1;
  assign stkz_lsu_req_o    = stkz_active;
  assign stkz_lsu_addr_o   = {stkz_ptrw_nxt, 2'h0};

  assign stkz_active_o     = stkz_active;      
  assign stkz_active       = (stkz_fsm_q == STKZ_ACTIVE);
  assign stkz_abort_o      = (stkz_fsm_q == STKZ_ABORT);

  // if new command pending, update this immediately so we can block further load/stores
  assign stkz_ptr_o        = cmd_pending ? cmd_wdata_q : {stkz_ptrw, 2'h0};
  assign stkz_base_o       = cmd_pending ? cmd_wbase32_q : {stkz_basew, 2'h0};

  assign ztop_rdata_o = {stkz_ptrw, 2'h0};
  assign ztop_rcap_o  = ztop_rcap;

  assign ztop_wbase32 = ztop_wfcap_i.base32;

  assign ztop_wtop33  = ztop_wfcap_i.top33;

  //     do we need to check permission as well?
  assign cmd_new       = ztop_wr_i & (cmd_cap_good | cmd_is_null_d);
  assign cmd_avail     = cmd_new || cmd_pending;
  assign cmd_go        = cmd_avail & (((stkz_fsm_q == STKZ_ACTIVE) && lsu_stkz_req_done_i) || 
                                       (stkz_fsm_q != STKZ_ACTIVE)); 

  assign cmd_is_null   = cmd_new ? cmd_is_null_d : cmd_is_null_q;
  assign cmd_wdata     = cmd_new ? ztop_wdata_i : cmd_wdata_q;
  assign cmd_wcap      = cmd_new ? full2regcap(ztop_wfcap_i) : cmd_wcap_q;
  assign cmd_wbase32   = cmd_new ? ztop_wbase32 : cmd_wbase32_q;

  assign cmd_cap_good  = ztop_wfcap_i.valid && (ztop_wtop33[32:2] >= ztop_wdata_i[31:2]);
  assign cmd_is_null_d = (ztop_wfcap_i == NULL_FULL_CAP) && (ztop_wdata_i == 32'h0);
  assign cmd_n2z       = cmd_wcap.valid & (cmd_wdata[31:2] == cmd_wbase32[31:2]);

  assign ptr_le_base   = (stkz_ptrw_nxt <= stkz_basew);
  assign stkz_start    = cmd_go && ~cmd_is_null && (cmd_wdata[31:2] != cmd_wbase32[31:2]);
  assign stkz_done     = lsu_stkz_req_done_i && ((~cmd_go & ptr_le_base) || (cmd_go && (cmd_n2z|cmd_is_null)));
  assign stkz_stop     = lsu_stkz_req_done_i && (unmasked_intr_i) && ~ptr_le_base;


  always_comb begin
    logic [3:0] tmp4;
    logic [8:0] addrmi9;
 
    if ((stkz_fsm_q == STKZ_IDLE) && stkz_start)
      stkz_fsm_d = STKZ_ACTIVE;
    else if ((stkz_fsm_q == STKZ_ACTIVE) & stkz_done)  // "normal" finish case (including sw-initiated stop)
      stkz_fsm_d = STKZ_IDLE;
    else if ((stkz_fsm_q == STKZ_ACTIVE) & stkz_stop)  // have to abort asynchly due to interrupt
      stkz_fsm_d = STKZ_ABORT;
    else if ((stkz_fsm_q == STKZ_ABORT) & stkz_start)
      stkz_fsm_d = STKZ_ACTIVE;    
    else if (stkz_fsm_q == STKZ_ABORT) 
      stkz_fsm_d = STKZ_IDLE;    // self clear by any furtherload/store activity
    else
      stkz_fsm_d = stkz_fsm_q;

    // clear tag if writing an ztop value with address == base
    cmd_wcap_untagged = cmd_wcap;
    cmd_wcap_untagged.valid = 1'b0;

    // QQQ we are doing this in lieu of a full set_address.
    //   note we only start an zeroization if tag is valid (which means addr >= base)
    ztop_rcap_nxt = ztop_rcap;
    addrmi9 = {stkz_ptrw_nxt, 2'b00} >> ztop_rcap.exp;
    tmp4    = update_temp_fields(ztop_rcap.top, ztop_rcap.base, addrmi9);
    ztop_rcap_nxt.top_cor  = tmp4[3:2];
    ztop_rcap_nxt.base_cor = tmp4[1:0];
    ztop_rcap_nxt.valid    = ztop_rcap.valid & ~stkz_done;
  end
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stkz_fsm_q    <= STKZ_IDLE;
      stkz_ptrw     <= 30'h0;
      stkz_ptrw_nxt <= 30'h0;
      stkz_basew    <= 30'h0;
      stkz_err_o    <= 1'b0;
      ztop_rcap     <= NULL_REG_CAP;
      cmd_pending   <= 1'b0;
      cmd_is_null_q <= 1'b0;
      cmd_wcap_q    <= NULL_REG_CAP;
      cmd_wdata_q   <= 32'h0;
      cmd_wbase32_q <= 32'h0;
    end else begin

      stkz_fsm_q <= stkz_fsm_d;

      // zcap is an WARL SCR
      //   - if active, only allow writing NULL to stop. Readback always return current progress
      //   - if not active, i
      //     - only allow writing tagged cap (legalized), which starts zeroization, however
      //     - speical case: write a tagged cap with addr == base will NOT start zeroization but 
      //       will clear tag on read
      //
      // if (stkz_start || (cmd_go & cmd_n2z)) begin
      if (cmd_go) begin
        stkz_ptrw <= cmd_wdata[31:2];
        ztop_rcap <= (cmd_go & cmd_n2z) ? cmd_wcap_untagged : cmd_wcap;
      end else if (stkz_active && lsu_stkz_req_done_i) begin
        stkz_ptrw <= stkz_ptrw_nxt; 
        ztop_rcap <= ztop_rcap_nxt;
      end

      // this is the captured hardware zeroization context, only updated for valid zerioation runs
      if (stkz_start) begin
        stkz_ptrw_nxt <= cmd_wdata[31:2] - 1;
        stkz_basew    <= cmd_wbase32[31:2];
      end else if (stkz_active && lsu_stkz_req_done_i && ~(stkz_done | stkz_stop)) begin
        stkz_ptrw_nxt <= stkz_ptrw_nxt - 1;
      end
       
      if (~stkz_active && stkz_start)
        stkz_err_o <= 1'b0;
      else if (lsu_stkz_resp_valid_i && lsu_stkz_resp_err_i)
        stkz_err_o <= 1'b1;

      if (cmd_go)
        cmd_pending <= 1'b0;       // clear
      else if (cmd_avail)
        cmd_pending <= 1'b1;       // latch command 

      if (cmd_new) cmd_is_null_q  <= cmd_is_null_d;
      if (cmd_new) cmd_wdata_q    <= ztop_wdata_i;
      if (cmd_new) cmd_wcap_q     <= full2regcap(ztop_wfcap_i);
      if (cmd_new) cmd_wbase32_q  <= ztop_wbase32;

    end
  end

endmodule
