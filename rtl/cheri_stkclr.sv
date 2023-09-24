// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


module cheri_stkclr (
   // Clock and Reset
  input  logic          clk_i,
  input  logic          rst_ni,

  // CSR register interface 
  input  logic          csr_stkclr_ptr_wr_i,
  input  logic [31:0]   csr_stkclr_ptr_wdata_i,
  input  logic [31:0]   csr_mshwm_i,

  input  logic          unmasked_intr_i,

  output logic          stkclr_active_o,
  output logic          stkclr_abort_o,
  output logic [31:0]   stkclr_ptr_o,
  output logic [31:0]   stkclr_base_o,
  output logic          stkclr_err_o,

  // LSU req/resp interface (to be multiplixed/qualified)
  input  logic          lsu_stkclr_resp_valid_i,
  input  logic          lsu_stkclr_resp_err_i,
  input  logic          lsu_stkclr_req_done_i,   
  output logic          stkclr_lsu_req_o,
  output logic          stkclr_lsu_we_o,
  output logic          stkclr_lsu_is_cap_o,
  output logic [31:0]   stkclr_lsu_addr_o,
  output logic [32:0]   stkclr_lsu_wdata_o,

  input  logic          snoop_lsu_req_done_i
);

  typedef enum logic [1:0] {STKCLR_IDLE, STKCLR_ACTIVE, STKCLR_ABORT} stkclr_fsm_t;

  stkclr_fsm_t  stkclr_fsm_d, stkclr_fsm_q;

  logic  [29:0] stkclr_ptr32, stkclr_ptr32_nxt, stkclr_base32;
  logic         stkclr_start, stkclr_done, stkclr_stop, stkclr_active;


  assign stkclr_lsu_wdata_o  = 33'h0;
  assign stkclr_lsu_is_cap_o = 1'b0;        // this means we are really writing 33'h0 to memory
  assign stkclr_lsu_we_o     = 1'b1;
  assign stkclr_lsu_req_o    = stkclr_active;
  assign stkclr_lsu_addr_o   = {stkclr_ptr32_nxt, 2'h0};

  assign stkclr_active_o     = stkclr_active;      
  assign stkclr_active       = (stkclr_fsm_q == STKCLR_ACTIVE);
  assign stkclr_abort_o      = (stkclr_fsm_q == STKCLR_ABORT);
  assign stkclr_ptr_o        = {stkclr_ptr32, 2'h0};
  assign stkclr_base_o       = {stkclr_base32, 2'h0};

  assign stkclr_start        = csr_stkclr_ptr_wr_i && (stkclr_fsm_q == STKCLR_IDLE) &&
                               (csr_mshwm_i != csr_stkclr_ptr_wdata_i);
  assign stkclr_done         = lsu_stkclr_req_done_i && (stkclr_ptr32_nxt <= stkclr_base32);
  assign stkclr_stop         = lsu_stkclr_req_done_i && unmasked_intr_i;

  always_comb begin
    if ((stkclr_fsm_q == STKCLR_IDLE) && stkclr_start)
      stkclr_fsm_d = STKCLR_ACTIVE;
    else if ((stkclr_fsm_q == STKCLR_ACTIVE) & stkclr_done)
      stkclr_fsm_d = STKCLR_IDLE;
    else if ((stkclr_fsm_q == STKCLR_ACTIVE) & stkclr_stop)
      stkclr_fsm_d = STKCLR_ABORT;
    else if ((stkclr_fsm_q == STKCLR_ABORT) & snoop_lsu_req_done_i)
      stkclr_fsm_d = STKCLR_IDLE;    // self clear by any furtherload/store activity
    else
      stkclr_fsm_d = stkclr_fsm_q;
  end
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stkclr_fsm_q     <= STKCLR_IDLE;
      stkclr_ptr32     <= 30'h0;
      stkclr_ptr32_nxt <= 30'h0;
      stkclr_base32    <= 30'h0;
      stkclr_err_o     <= 1'b0;
    end else begin

      stkclr_fsm_q <= stkclr_fsm_d;

      if (stkclr_start)
        stkclr_ptr32 <= csr_stkclr_ptr_wdata_i[31:2];
      else if (stkclr_active && lsu_stkclr_req_done_i) 
        stkclr_ptr32  <= stkclr_ptr32_nxt; 

      if (stkclr_start)
        stkclr_ptr32_nxt <= csr_stkclr_ptr_wdata_i[31:2] - 1;
      else if (stkclr_active && lsu_stkclr_req_done_i && ~(stkclr_done | stkclr_stop))
        stkclr_ptr32_nxt  <= stkclr_ptr32_nxt - 1;
       
      if (stkclr_start)
        stkclr_base32 <= csr_mshwm_i[31:2];      // capture curent stack high watermark
  
      if (stkclr_start)
        stkclr_err_o <= 1'b0;
      else if (lsu_stkclr_resp_valid_i && lsu_stkclr_resp_err_i)
        stkclr_err_o <= 1'b1;

    end
  end

endmodule
