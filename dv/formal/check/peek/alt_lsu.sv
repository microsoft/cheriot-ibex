// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// SPDX-License-Identifier: Apache-2.0


/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module alt_lsu import ibex_pkg::*; import cheri_pkg::*; #(
  parameter bit CHERIoTEn = 1'b1,
  parameter bit MemCapFmt = 1'b0,
  parameter bit CheriTBRE = 1'b0
)(
  input  logic         cheri_pmode_i,

  // data interface
  input  logic         data_rvalid_i,
  input  logic         data_err_i,
  input  logic [32:0]  data_rdata_i,         // kliu

  output reg_cap_t     lsu_rcap_o,           // kliu
  output logic [32:0]  lsu_rdata_o,          // requested data                   -> to ID/EX

  // exception signals
  input logic [31:8] rdata_q,
  input logic [1:0] rdata_offset_q,
  input logic [1:0] data_type_q,
  input logic data_sign_ext_q,
  input logic data_we_q,
  input logic pmp_err_q,
  input logic lsu_err_q,
  input logic outstanding_resp_q,
  input logic resp_is_cap_q,
  input logic cheri_err_q,
  input logic [3:0] resp_lc_clrperm_q,
  input cap_rx_fsm_t cap_rx_fsm_q,
  input logic cap_lsw_err_q,
  input logic [32:0] cap_lsw_q
);
  logic [32:0]  data_rdata_ext;

  logic [32:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         data_or_pmp_err;

  /////////////////////
  // RData alignment //
  /////////////////////

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[32:0];
      2'b01:   rdata_w_ext = {1'b0, data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {1'b0, data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {1'b0, data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext =  data_rdata_i[32:0];
    endcase
  end

  ////////////////////
  // Sign extension //
  ////////////////////

  // sign extension for half words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
        end
      end

      default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
        end
      end

      default: rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = {1'b0, rdata_h_ext};
      2'b10,2'b11: data_rdata_ext = {1'b0, rdata_b_ext};
      default:     data_rdata_ext = rdata_w_ext;
    endcase // case (data_type_q)
  end

  /////////////
  // Outputs //
  /////////////
  assign data_or_pmp_err    = lsu_err_q | data_err_i | pmp_err_q | (cheri_pmode_i & 
                              (cheri_err_q | (resp_is_cap_q & cap_lsw_err_q)));

  // output to register file
  if (CHERIoTEn & ~MemCapFmt) begin : gen_memcap_rd_fmt0
    assign lsu_rdata_o = (cheri_pmode_i & resp_is_cap_q) ? cap_lsw_q : data_rdata_ext;
    assign lsu_rcap_o  = (resp_is_cap_q && data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) && (~data_or_pmp_err)) ?
                         mem2regcap_fmt0(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q) : NULL_REG_CAP;
  end else if (CHERIoTEn) begin : gen_memcap_rd_fmt1
    assign lsu_rdata_o = (cheri_pmode_i & resp_is_cap_q) ? mem2regaddr_fmt1(data_rdata_ext, cap_lsw_q, lsu_rcap_o): data_rdata_ext;
    assign lsu_rcap_o  = (resp_is_cap_q && data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) && (~data_or_pmp_err)) ?
                         mem2regcap_fmt1(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q) : NULL_REG_CAP;
  end else begin : gen_no_cap_rd
    assign lsu_rdata_o = data_rdata_ext;
    assign lsu_rcap_o  = NULL_REG_CAP;
  end
endmodule
