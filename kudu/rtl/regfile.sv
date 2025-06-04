
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module regfile import super_pkg::*; import cheri_pkg::*; #(
  parameter int unsigned NRegs      = 32,
  parameter bit          CHERIoTEn  = 1'b1
) (
   // Clock and Reset
  input  logic             clk_i,
  input  logic             rst_ni,

  //Read ports
  input  rf_raddr2_t       raddr2_p0_i,
  input  rf_raddr2_t       raddr2_p1_i,
  output rf_rdata2_t       rdata2_p0_o,
  output rf_rdata2_t       rdata2_p1_o,

  // Write ports
  input  logic [4:0]       waddr0_i,
  input  logic [RegW-1:0]  wdata0_i,
  input  logic             we0_i,  

  input  logic [4:0]       waddr1_i,
  input  logic [RegW-1:0]  wdata1_i,
  input  logic             we1_i,   

  input  logic [4:0]       waddr2_i,
  input  logic [RegW-1:0]  wdata2_i,
  input  logic             we2_i,    

  // Revocation tag clearing interface
  input  logic             trvk_en_i,
  input  logic             trvk_clrtag_i,
  input  logic [4:0]       trvk_addr_i
);

  logic [RegW-1:0] rf_reg   [NRegs-1:0];
  logic [RegW-1:0] rf_reg_q [NRegs-1:1];
  
  logic [NRegs-1:1] we0_dec, we1_dec, we2_dec, trvk_clrtag_dec;

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NRegs; i++) begin : g_rf_flops
    logic [RegW-1:0] clrtag_mask;

    assign we0_dec[i]  = (waddr0_i == 5'(i)) & we0_i;
    assign we1_dec[i]  = (waddr1_i == 5'(i)) & we1_i;
    assign we2_dec[i]  = (waddr2_i == 5'(i)) & we2_i;

    assign trvk_clrtag_dec[i] = CHERIoTEn & trvk_en_i & trvk_clrtag_i & (trvk_addr_i == 5'(i));
    assign clrtag_mask = {~trvk_clrtag_dec[i], {REG_TAG{1'b1}}};

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q[i] <= 0;
      end else if (we2_dec[i]) begin
        rf_reg_q[i] <= wdata2_i & clrtag_mask;
      end else if (we1_dec[i]) begin
        rf_reg_q[i] <= wdata1_i & clrtag_mask;
      end else if (we0_dec[i]) begin
        rf_reg_q[i] <= wdata0_i & clrtag_mask;
      end else if (trvk_clrtag_dec[i]) begin
        rf_reg_q[i] <= rf_reg_q[i] & clrtag_mask;
      end 
    end
  end // g_rf_flops

  assign rf_reg[0]   = 32'h0;
  for (genvar i=1; i<NRegs; i++) begin
    assign rf_reg[i] = rf_reg_q[i];         
  end

  assign rdata2_p0_o.d0 =  rf_reg[raddr2_p0_i.a0];
  assign rdata2_p0_o.d1 =  rf_reg[raddr2_p0_i.a1];
  assign rdata2_p1_o.d0 =  rf_reg[raddr2_p1_i.a0];
  assign rdata2_p1_o.d1 =  rf_reg[raddr2_p1_i.a1];

endmodule
