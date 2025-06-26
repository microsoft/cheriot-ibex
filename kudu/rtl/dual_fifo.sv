// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Pipelined Fifo, dual-issue read & write
//   Interface protocol:
//   -- this FIFO use a valid-ready handshaking on both sides
//      -- rdy indicates room on the receiving end (rdy for 0, 1, or 2 transactions) 
//      -- valid indicates new data availability on the transmittingr end (data available for 0, 1 or 2 transcations)
//   -- Legal values for valid/rdy signals:
//      -- 2'b11 (vaid 2/rdy 2)
//      -- 2'b01 (valid 1/rdy 1)
//      -- 2'b00 (nop)
//      -- 2'b10 is illegal
//   -- The design will only drive rd_valid_o and wr_rday_o with legal values.
//   -- The write party can assert valid2 when only rdy1 or rdy0 available, but it must follow the backpressure
//   -- The read party should generate rd_rdy based rd_valid from the design, and not assert rdy2 if design
//      asserts valid1. Otherwise only 1 read happens.
//   
//
module dual_fifo # (
  parameter int unsigned Depth        = 2,    // must be power of 2
  parameter int unsigned Width        = 32,
  parameter bit          PipelineRead = 1'b0  
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  logic              flush_i,

  input  logic [1:0]        wr_valid_i,
  input  logic [Width-1:0]  wr_data0_i,    // 1st sequential data input
  input  logic [Width-1:0]  wr_data1_i,    // 2nd sequential data input
  output logic [1:0]        wr_rdy_o, 

  input  logic [1:0]        rd_rdy_i,
  output logic [1:0]        rd_valid_o,
  output logic [Width-1:0]  rd_data0_o,    // 1st sequential data output
  output logic [Width-1:0]  rd_data1_o    // 2nd sequential data output
  );

  localparam int unsigned      PtrW    = $clog2(Depth)+1;
  localparam logic [PtrW-1:0]  DepthM1 = Depth-1;
  localparam logic [PtrW-1:0]  DepthM2 = Depth-2;
  
  logic [PtrW-1:0] wr_ptr_q, wr_ptr_p1, wr_ptr_p2, wr_ptr_nxt;
  logic [PtrW-1:0] rd_ptr_q, rd_ptr_p1, rd_ptr_p2, rd_ptr_nxt;
  logic [PtrW-1:0] cur_wr_depth, cur_rd_depth;

  logic [PtrW-2:0] wr_mem_addr[2];
  logic [PtrW-2:0] rd_mem_addr[2];

  logic [Width-1:0] fifo_mem[Depth];

  logic [1:0] wr_rdy, rd_valid;
  logic [1:0] wr_data_en;

  // I/O assigments
  assign wr_rdy_o   = wr_rdy;
  assign rd_valid_o = rd_valid;

  // pointer arithmetic
  assign wr_ptr_p1 = wr_ptr_q + 1;
  assign wr_ptr_p2 = wr_ptr_q + 2;
  assign rd_ptr_p1 = rd_ptr_q + 1;
  assign rd_ptr_p2 = rd_ptr_q + 2;

  assign cur_wr_depth  = PipelineRead ? (wr_ptr_q - rd_ptr_nxt) : (wr_ptr_q - rd_ptr_q);  
  assign cur_rd_depth  = wr_ptr_q - rd_ptr_q;

  // actual FIFO storage addresses
  assign wr_mem_addr[0] = wr_ptr_q[PtrW-2:0];
  assign wr_mem_addr[1] = wr_ptr_p1[PtrW-2:0];

  assign rd_mem_addr[0] = rd_ptr_q[PtrW-2:0];
  assign rd_mem_addr[1] = rd_ptr_p1[PtrW-2:0];

  // output signals
  // assign wr_rdy[1] = (cur_wr_depth <= DepthM2) | flush_i;
  // assign wr_rdy[0] = (cur_wr_depth <= DepthM1) | flush_i;
  assign wr_rdy[1] = (cur_wr_depth <= DepthM2);
  assign wr_rdy[0] = (cur_wr_depth <= DepthM1);

  assign rd_valid[1] = (cur_rd_depth >= 2);
  assign rd_valid[0] = (cur_rd_depth >= 1);

  assign rd_data0_o = fifo_mem[rd_mem_addr[0]];
  assign rd_data1_o = fifo_mem[rd_mem_addr[1]];

  // extended read and write pointers
  always_comb begin
    if ((rd_valid[1:0] == 2'b11) &&(rd_rdy_i == 2'b11))
      rd_ptr_nxt = rd_ptr_p2;          // read 2
    else if (rd_valid[0] && rd_rdy_i[0])
      rd_ptr_nxt = rd_ptr_p1;          // read 1
    else 
      rd_ptr_nxt = rd_ptr_q;

    // if (flush_i) begin
    //  wr_data_en = 2'b00;
    // end else 
    if ((wr_rdy[1:0] == 2'b11) && (wr_valid_i == 2'b11)) begin
      wr_ptr_nxt = wr_ptr_p2;          // write 2
      wr_data_en = 2'b11;
    end else if (wr_rdy[0] && wr_valid_i[0]) begin
      wr_ptr_nxt = wr_ptr_p1;          // write 1
      wr_data_en = 2'b01;
    end else begin
      wr_ptr_nxt = wr_ptr_q;
      wr_data_en = 2'b00;
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
  for (genvar i=0; i < Depth; i++) begin : gen_fifo_mem
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fifo_mem[i] <= 0;
      end else begin
        if (wr_data_en[0] && (i == wr_mem_addr[0]))
          fifo_mem[i] <= wr_data0_i;
        else if (wr_data_en[1] && (i == wr_mem_addr[1]))
          fifo_mem[i] <= wr_data1_i;
      end
    end
  end

  // flagging which FIFO entry is being update (so we can extend the fifo memory externally)

`ifndef SYNTHESIS
  logic signed [7:0]  wr_num, rd_num;
  logic signed [7:0]  fifo_level;
  logic               illegal_wr, illegal_rd;
  logic signed [31:0] wr_total, rd_total;


  assign wr_num = (wr_rdy_o[1] & wr_valid_i[1]) + (wr_rdy_o[0] & wr_valid_i[0]);
  assign rd_num = (rd_rdy_i[0] & rd_valid_o[0]) + (rd_rdy_i[1] & rd_valid_o[1]);

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

  assign illegal_wr = wr_valid_i[1] & ~wr_valid_i[0];
  assign illegal_rd = rd_rdy_i[1] & ~rd_rdy_i[0];
`endif

`ifdef FORMAL
  AssumeWrInputLegal: assume property (@(posedge clk_i) wr_valid_i[1] |-> wr_valid_i[0]);
  AssumeRdInputLegal: assume property (@(posedge clk_i) rd_rdy_i[1] |-> rd_rdy_i[0]);
//  AssumeFlushLegal:   assume property (@(posedge clk_i) flush_i |-> 
//                                       ((rd_rdy_i == 2'b00) && (wr_valid_i == 2'b00)));

  AssertWrOutputLegal: assert property (@(posedge clk_i) wr_rdy_o[1] |-> wr_rdy_o[0]);
  AssertRdOutputLegal: assert property (@(posedge clk_i) rd_valid_o[1] |-> rd_valid_o[0]);

  AssertFifoUnderrun: assert property (@(posedge clk_i) (fifo_level >= 0));
  AssertFifoOverrun: assert property (@(posedge clk_i) (fifo_level <= Depth));
  
`endif

endmodule

