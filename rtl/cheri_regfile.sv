// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheri_regfile import cheri_pkg::*; #(
  parameter int unsigned NREGS = 32,
  parameter int unsigned NCAPS = 16,
  parameter bit          CheriPPLBC = 1'b0
) (
   // Clock and Reset
  input  logic         clk_i,
  input  logic         rst_ni,

  //Read port R1
  input  logic  [4:0]  raddr_a_i,
  output logic [31:0]  rdata_a_o,
  output reg_cap_t     rcap_a_o,

  //Read port R2
  input  logic  [4:0]  raddr_b_i,
  output logic [31:0]  rdata_b_o,
  output reg_cap_t     rcap_b_o,

  // Write port W1
  input  logic [4:0]   waddr_a_i,
  input  logic [31:0]  wdata_a_i,
  input  reg_cap_t     wcap_a_i,
  input  logic         we_a_i,         // we always write both cap & data in parallel

  // Tag reservation and revocation port
  output logic [31:0]  reg_rdy_o,
  input  logic [4:0]   trvk_addr_i,
  input  logic         trvk_en_i,
  input  logic         trvk_clrtag_i,
  input  logic [4:0]   trsv_addr_i,
  input  logic         trsv_en_i
);


  logic [31:0] rf_reg   [NREGS-1:0];
  logic [31:0] rf_reg_q [NREGS-1:1];
  reg_cap_t    rf_cap   [NCAPS-1:0] ;
  reg_cap_t    rf_cap_q [NCAPS-1:1] ;

  logic [NREGS-1:1]       we_a_dec;
  logic [NREGS-1:1]       trvk_dec, trsv_dec;
  logic [31:0]            reg_rdy_vec;

  always_comb begin : we_a_decoder
    for (int unsigned i = 1; i < NREGS; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
      trvk_dec[i] = CheriPPLBC ? (trvk_addr_i == 5'(i)) : 1'b0;
      trsv_dec[i] = CheriPPLBC ? (trsv_addr_i == 5'(i)) : 1'b0;
    end
  end

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NREGS; i++) begin : g_rf_flops
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q[i] <= 32'h0;
      end else if (we_a_dec[i]) begin
        rf_reg_q[i] <= wdata_a_i;
      end
    end
  end

  assign rf_reg[0] = 32'h0;
  for (genvar i=1; i<NREGS ; i++) begin
    assign rf_reg[i] = rf_reg_q[i];
  end

  assign rdata_a_o = rf_reg[raddr_a_i];
  assign rdata_b_o = rf_reg[raddr_b_i];

  // capability meta data (MSW)
  for (genvar i = 1; i < NCAPS; i++) begin : g_cap_flops
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_cap_q[i] <= NULL_REG_CAP;
      end else if (CheriPPLBC & trvk_dec[i] & trvk_en_i & trvk_clrtag_i ) begin
        // prioritize revocation (later in pipeline)
        rf_cap_q[i].valid <= 1'b0;
      end else if (we_a_dec[i]) begin
        rf_cap_q[i] <= wcap_a_i;
      end
    end
  end

  assign rf_cap[0] = NULL_REG_CAP;
  for (genvar i=1; i<NCAPS ; i++) begin
    assign rf_cap[i] = rf_cap_q[i];
  end

  assign rcap_a_o = (raddr_a_i < NCAPS) ? rf_cap[raddr_a_i] : NULL_REG_CAP;
  assign rcap_b_o = (raddr_b_i < NCAPS) ? rf_cap[raddr_b_i] : NULL_REG_CAP;

  for (genvar i = 0; i < 32; i++) begin : g_regrdy
    if (~CheriPPLBC || (i==0) || (i>=NCAPS)) begin
      assign reg_rdy_vec[i] = 1'b1;
    end else begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
          reg_rdy_vec[i] <= 1'b1;
        else if (trvk_dec[i] & trvk_en_i)
          reg_rdy_vec[i] <= 1'b1;
        else if (trsv_dec[i] & trsv_en_i)
          reg_rdy_vec[i] <= 1'b0;
      end  // always_ff
    end
  end   // for generate

  assign reg_rdy_o = reg_rdy_vec;

endmodule
