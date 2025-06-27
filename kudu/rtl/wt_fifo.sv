// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Write-through Fifo, single-issue 
//   Interface protocol:
//   -- this FIFO use a valid-ready handshaking on both sides
//   
//
module wt_fifo # (
  parameter int unsigned Depth       = 2,    // must be power of 2
  parameter int unsigned Width       = 32
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  logic              flush_i,

  input  logic              wr_valid_i,
  input  logic [Width-1:0]  wr_data_i,
  output logic              wr_rdy_o, 

  input  logic              rd_rdy_i,
  output logic              rd_valid_o,
  output logic [Width-1:0]  rd_data_o
  );

  localparam int unsigned      PtrW    = $clog2(Depth)+1;
  localparam logic [PtrW-1:0]  DepthM1 = Depth-1;
  
  logic [PtrW-1:0] wr_ptr_q, wr_ptr_p1, wr_ptr_nxt;
  logic [PtrW-1:0] rd_ptr_q, rd_ptr_p1, rd_ptr_nxt;
  logic [PtrW-1:0] cur_wr_depth, cur_rd_depth;

  logic [PtrW-2:0] wr_mem_addr;
  logic [PtrW-2:0] rd_mem_addr;

  logic [Width-1:0] fifo_mem[Depth];

  logic wr_rdy, rd_valid;
  logic wr_data_en;
  logic fifo_empty;

  // I/O assigments
  assign wr_rdy_o   = wr_rdy;
  assign rd_valid_o = rd_valid;

  // pointer arithmetic
  assign wr_ptr_p1 = wr_ptr_q + 1;
  assign rd_ptr_p1 = rd_ptr_q + 1;

  assign cur_wr_depth  = wr_ptr_q - rd_ptr_q;  
  assign cur_rd_depth  = wr_ptr_q - rd_ptr_q;

  // actual FIFO storage addresses
  assign wr_mem_addr = wr_ptr_q[PtrW-2:0];
  assign rd_mem_addr = rd_ptr_q[PtrW-2:0];

  // output signals
  assign fifo_empty = (cur_rd_depth == 0);
  assign wr_rdy     = (cur_wr_depth <= DepthM1);
  assign rd_valid   = ~fifo_empty | wr_valid_i;
  assign rd_data_o  = fifo_empty ? wr_data_i : fifo_mem[rd_mem_addr];

  // extended read and write pointers
  always_comb begin
    if (rd_valid && rd_rdy_i)
      rd_ptr_nxt = rd_ptr_p1;
    else 
      rd_ptr_nxt = rd_ptr_q;

    if (wr_rdy && wr_valid_i) begin
      wr_ptr_nxt = wr_ptr_p1;    
      wr_data_en = 1'b1;
    end else begin
      wr_ptr_nxt = wr_ptr_q;
      wr_data_en = 1'b0;
    end

  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr_ptr_q <= 0;
      rd_ptr_q <= 0;
    end else begin
      if (flush_i) begin
        wr_ptr_q <= 0;
        rd_ptr_q <= 0;
      end else begin
        wr_ptr_q <= wr_ptr_nxt;
        rd_ptr_q <= rd_ptr_nxt;
      end
    end
  end
 
  // Generate storage flops and write enable logic
  // Tracking regWr requests to maintain WaW status  


  for (genvar i=0; i < Depth; i++) begin : gen_fifo_mem
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fifo_mem[i] <= 0;
      end else if (wr_data_en && (i == wr_mem_addr)) begin
        fifo_mem[i] <= wr_data_i;
      end
    end
  end

`ifndef SYNTHESIS
  logic signed [7:0]  wr_num, rd_num;
  logic signed [7:0]  fifo_level;
  logic signed [31:0] wr_total, rd_total;

  assign wr_num = wr_rdy_o & wr_valid_i; 
  assign rd_num = rd_rdy_i & rd_valid_o;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      fifo_level <= 0;
      wr_total   <= 0;
      rd_total   <= 0;
    end else begin
      if (flush_i) begin
        fifo_level <= 0;
        wr_total   <= 0;
        rd_total   <= 0;
      end else begin
        fifo_level <= fifo_level + wr_num - rd_num;
        wr_total   <= wr_total + wr_num;
        rd_total   <= rd_total + rd_num;
      end
     
    end
  end 

`endif

`ifdef FORMAL

  AssertFifoUnderrun: assert property (@(posedge clk_i) (fifo_level >= 0));
  AssertFifoOverrun: assert property (@(posedge clk_i) (fifo_level <= Depth));
  
`endif

endmodule

