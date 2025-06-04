// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheri_trvk_stage import cheri_pkg::*; #(
  parameter int unsigned HeapBase  = 32'h2001_0000,
  parameter int unsigned TSMapSize = 1024
) (
   // Clock and Reset
  input  logic         clk_i,
  input  logic         rst_ni,

  input  logic         clc_valid_i,
  input  logic [4:0]   clc_rd_i,
  input  logic         clc_err_i,
  input  reg_cap_t     clc_rcap_i,

  output logic [4:0]   trvk_addr_o,
  output logic         trvk_en_o,
  output logic         trvk_clrtag_o,
  output logic         trvk_outstanding_o,

  output logic         tsmap_cs_o,
  output logic [15:0]  tsmap_addr_o,
  input  logic [31:0]  tsmap_rdata_i
);

  reg_cap_t    in_cap_q;
  op_cap_t     tmp_ocap;

  logic [2:0]  clc_valid_q, cap_good_q;
  logic        cap_good;
  logic [4:0]  trsv_addr;
  logic [4:0]  trsv_addr_q[2:0];
  logic        trvk_status;

  logic [31:0] base32;
  logic [31:0] tsmap_ptr;
  logic  [4:0] bitpos_q; // bit index in a 32-bit word
  logic        range_ok;
  logic  [2:1] range_ok_q;

  assign tmp_ocap  = reg2opcap(in_cap_q);
  assign base32    = 32'(get_bound33(tmp_ocap.base9, {2{tmp_ocap.base_cor}}, tmp_ocap.exp, tmp_ocap.addr));
  assign tsmap_ptr = (base32 - HeapBase) >> 3;

  assign tsmap_addr_o  = tsmap_ptr[15:5];

  // not a sealling cap and pointing to valid TSMAP range
  assign range_ok      = (tsmap_ptr[31:5] <= TSMapSize) && 
                         ~((in_cap_q.cperms[4:3]==2'b00) && (|in_cap_q.cperms[2:0]));
  assign tsmap_cs_o    = clc_valid_q[0]  & cap_good_q[0];

  assign trvk_en_o     =  clc_valid_q[2];
  assign trvk_clrtag_o =  trvk_status & cap_good_q[2] & range_ok_q[2];
  assign trvk_addr_o   =  trsv_addr_q[2];

  assign cap_good =  clc_valid_i & ~clc_err_i & clc_rcap_i.valid;

  // notify the issuer about any outstanding trvk operations
  assign trvk_outstanding_o = (|clc_valid_q);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      clc_valid_q     <= 0;
      cap_good_q      <= 0;
      in_cap_q        <= NULL_REG_CAP;
      bitpos_q        <= 0;
      trvk_status     <= 1'b0;
      range_ok_q      <= 0;
      trsv_addr_q[0]  <= 5'b0;
      trsv_addr_q[1]  <= 5'b0;
      trsv_addr_q[2]  <= 5'b0;
    end else begin
      // control signal per stage
      clc_valid_q     <= {clc_valid_q[1:0], clc_valid_i};
      cap_good_q      <= {cap_good_q[1:0], cap_good};
      trsv_addr_q[0]  <= clc_rd_i;
      trsv_addr_q[1]  <= trsv_addr_q[0];
      trsv_addr_q[2]  <= trsv_addr_q[1];

      // stage 0 status: register loaded cap
      if (clc_valid_i & ~clc_err_i) begin
        in_cap_q    <= clc_rcap_i;
      end

      // stage 1 status:
      bitpos_q      <= tsmap_ptr[4:0];
      range_ok_q[1] <= range_ok;

      // stage 2: index map data
      range_ok_q[2] <= range_ok_q[1];
      trvk_status   <= tsmap_rdata_i[bitpos_q];
    end
  end

endmodule
