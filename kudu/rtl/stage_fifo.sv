// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Timing-optimized 2-deep pipelined Fifo, dual-issue
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
module stage_fifo # (
  parameter int unsigned Width   = 32,
  parameter bit          PeekMem = 1'b0
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
  output logic [Width-1:0]  rd_data1_o,    // 2nd sequential data output
  output logic              mema_is0_o,   
  output logic [1:0]        wr_mema_o,
  output logic [1:0]        wr_memb_o,
  output logic              wr_ptr_o,
  output logic [Width-1:0]  mema_o,        // mem location 0 content
  output logic [Width-1:0]  memb_o         // mem location 1 content
  );

  localparam int unsigned FifoDepth = 2;
  
  logic  wr_ptr_q, wr_ptr_nxt;
  logic  rd_ptr_q, rd_ptr_nxt;
  logic  full_stat_q;

  logic have0, have1, have2, have1or2, have0or1;
  logic read0, read1, read2, read1or2;
  logic write0, write1, write2, write1or2;

  logic write_room0, write_room1, write_room2;

  logic  wr_mem_addr[2];
  logic  rd_mem_addr[2];

  logic [Width-1:0] fifo_mem[2];

  logic [1:0] wr_rdy, rd_valid;
  logic [1:0] wr_data_en;

  // I/O assigments
  assign wr_rdy_o   = wr_rdy;
  assign rd_valid_o = rd_valid;
  assign wr_ptr_o   = wr_ptr_q;

  // pointer arithmetic

  // actual FIFO storage addresses
  assign wr_mem_addr[0] = wr_ptr_q;
  assign wr_mem_addr[1] = ~wr_ptr_q;

  assign rd_mem_addr[0] = rd_ptr_q;
  assign rd_mem_addr[1] = ~rd_ptr_q;

  // output signals
  assign read0    = (rd_rdy_i == 2'b00);
  assign read1    = (rd_rdy_i == 2'b01);
  assign read2    = (rd_rdy_i == 2'b11);
  assign read1or2 = rd_rdy_i[0];

  assign write0    = (wr_valid_i == 2'b00);
  assign write1    = (wr_valid_i == 2'b01);
  assign write2    = (wr_valid_i == 2'b11);
  assign write1or2 = wr_valid_i[0];

  assign have0    = ~full_stat_q & (wr_ptr_q == rd_ptr_q);
  assign have1    = (wr_ptr_q != rd_ptr_q);
  assign have2    = full_stat_q;
  assign have0or1 = ~full_stat_q;
  assign have1or2 = have1 | have2;

  assign write_room2 = have0 | (have1 & read1or2) | (have2 & read2);
  assign write_room1 = (have1 & read0) | (have2 & read1);
  assign write_room0 = have2 & read0;

  assign wr_rdy[1] = write_room2;
  assign wr_rdy[0] = have0 | have1 | (have2 && read1or2);  // this should be eual to room1 or room2

  assign rd_valid[1] = have2;
  assign rd_valid[0] = have2 | have1;

  assign rd_data0_o = fifo_mem[rd_mem_addr[0]];
  assign rd_data1_o = fifo_mem[rd_mem_addr[1]];

  always_comb begin
    if ((read1 & have1or2) | (read2 & have1)) 
      rd_ptr_nxt = ~rd_ptr_q;
    else 
      rd_ptr_nxt = rd_ptr_q;
  
    if ((write_room1 & (write1 | write2)) || (write_room2 & write1))
      wr_ptr_nxt = ~wr_ptr_q;
    else 
      wr_ptr_nxt = wr_ptr_q;

    if (write_room2 & write2)
      wr_data_en = 2'b11;
    else if (write_room1 & write1or2)  
      wr_data_en = 2'b01;
    else if (write_room2 & write1)
      wr_data_en = 2'b01;
    else 
      wr_data_en = 2'b00;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr_ptr_q <= 0;
      rd_ptr_q <= 0;
      full_stat_q <= 1'b0;
    end else begin
      if (flush_i) begin
        wr_ptr_q <= 0;
        rd_ptr_q <= 0;
        full_stat_q <= 1'b0;
      end else begin
        wr_ptr_q <= wr_ptr_nxt;
        rd_ptr_q <= rd_ptr_nxt;

        if ((write_room1 & write1or2) | (write_room2 & write2))
          full_stat_q <= 1'b1;
        else if (~write_room0)
          full_stat_q <= 1'b0;
      end
    end
  end
  
  // Generate storage flops and write enable logic
  for (genvar i=0; i < 2; i++) begin : gen_fifo_mem
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

  // peak into fifo mem registers to provide an faster timing path
  assign mema_is0_o = ~rd_ptr_q;     // mema == data_rdata0 (early)

  if (PeekMem) begin : gen_peek
    assign mema_o    = fifo_mem[0];
    assign memb_o    = fifo_mem[1];
    assign wr_mema_o = {(wr_data_en[1] && (wr_mem_addr[1] == 0)), (wr_data_en[0] && (wr_mem_addr[0] == 0))}; 
    assign wr_memb_o = {(wr_data_en[1] && (wr_mem_addr[1] == 1)), (wr_data_en[0] && (wr_mem_addr[0] == 1))};
  end else begin : gen_no_peek
    assign mema_o    = Width'(0);
    assign memb_o    = Width'(0);
    assign wr_mema_o = 1'b0;
    assign wr_memb_o = 1'b0;
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
  AssertFifoOverrun:  assert property (@(posedge clk_i) (fifo_level <= FifoDepth));

  AssertWrRdy0:    assert property (@(posedge clk_i) (wr_rdy[0] == (write_room1 | write_room2)));

  AssertFifoLeve2: assert property (@(posedge clk_i) (have2 == (fifo_level == 2)));
  AssertFifoLeve1: assert property (@(posedge clk_i) (have1 == (fifo_level == 1)));
  AssertFifoLeve0: assert property (@(posedge clk_i) (have0 == (fifo_level == 0)));

  AssertWriteNum2:  assert property (@(posedge clk_i) ((wr_data_en == 2'b11) == (wr_num == 2)));
  AssertWriteNum1:  assert property (@(posedge clk_i) ((wr_data_en == 2'b01) == (wr_num == 1)));
  
`endif

endmodule

