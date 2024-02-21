// Copyright Microsoft Corporation

// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


`define IBEX_DII_INSN_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_rdata_dii
`define IBEX_DII_ACK_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_ack
`define IBEX_DII_PC_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_pc;
`define IBEX_TOP_PATH dut.u_ibex_top

module dii_if (
  input  logic         clk_i,
  input  logic         rst_ni,

  // DII generator interface
  input  logic [31:0]  dii_insn_0_i,
  input  logic [31:0]  dii_insn_1_i,
  output logic [31:0]  dii_pc_o,
  output logic         dii_ack_0_o,
  output logic         dii_ack_1_o
  );

  localparam MaxFlushCnt = 1;

  logic        rvfi_valid;
  logic        rvfi_trap;
  logic [31:0] rvfi_insn, rvfi_pc;

  logic        dii_ack, dii_sel0;
  logic [31:0] dii_insn;
  logic [63:0] hqueue[$];

  `ifdef DII_SIM
    assign dii_sel0 = 1'b1;  // QQQ for now - should from pc decoding

    assign dii_insn = dii_sel0 ? dii_insn_0_i : dii_insn_1_i;
    assign `IBEX_DII_INSN_PATH = dii_insn;

    assign dii_ack     = `IBEX_DII_ACK_PATH;
    assign dii_ack_0_o = dii_ack & dii_sel0;
    assign dii_ack_1_o = dii_ack & ~dii_sel0;

    assign dii_pc_o = `IBEX_DII_PC_PATH;

    // RVFI interface
    assign rvfi_valid = `IBEX_TOP_PATH.rvfi_valid;
    assign rvfi_trap  = `IBEX_TOP_PATH.rvfi_trap;
    assign rvfi_pc    = `IBEX_TOP_PATH.rvfi_pc_rdata;
    assign rvfi_insn  = `IBEX_TOP_PATH.rvfi_insn;
  `else
    assign dii_insn    = 32'h0;
    assign dii_ack     = 1'b0;
    assign dii_ack_0_o = 1'b0;
    assign dii_ack_1_o = 1'b0;
    assign dii_pc_o    = 32'h0;

    assign rvfi_valid = 1'b0;
    assign rvfi_trap  = 1'b0;
    assign rvfi_pc    = 32'h0;
    assign rvfi_insn  = 32'h0;
  `endif

  initial begin
    int   flush_cnt;
    logic flush_active;

    @(posedge rst_ni);
    hqueue = {};

    while (1) begin
      @(posedge clk_i);
      if (dii_ack) 
        hqueue = {hqueue, {dii_pc_o, dii_insn}};    // enqeue

      if (rvfi_valid) begin
        assert (hqueue.size() >= 1) 
          else $error("dii_if: holding queue empty");

        if (~flush_active) begin
          assert(hqueue[0] == {rvfi_pc, rvfi_insn}) 
            else $error("dii_if: holding queue read mismatch");
          hqueue = hqueue[1:$];     
        end else begin  // exception entry found, flush holding queue
          flush_cnt  = 0;
          while (1) begin
            if (hqueue.size() == 0) break;
            if (hqueue[0] == {rvfi_pc, rvfi_insn}) begin
              hqueue       = hqueue[1:$];     
              flush_active = 1'b0;
              break;
            end else begin 
              flush_cnt += 1;
              hqueue = hqueue[1:$];     
            end
          end // while 

          assert (!flush_active && (flush_cnt<=MaxFlushCnt)) 
            else $error("dii_if: holding queue flush error");
        end
        
        // in ibex, only need to flush/resync the hqueue in the event of a WB-stage trap 
        if (rvfi_trap) flush_active = 1'b1;
      end
  
    end
  end

endmodule
