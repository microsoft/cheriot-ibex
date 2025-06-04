// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch Fifo for 32 bit memory interface
 *
 * input port: send address and data to the FIFO
 * clear_i clears the FIFO for the following cycle, including any new request
 */

module fetch_fifo64 import super_pkg::*; #(
  parameter int unsigned NUM_REQS       = 2,
  parameter bit          UnalignedFetch = 1'b1
) (
  input  logic                clk_i,
  input  logic                rst_ni,

  // control signals
  input  logic                clear_i,   // clears the contents of the FIFO
  output logic [NUM_REQS-1:0] busy_o,

  // input port
  input  logic                in_valid_i,
  input  logic [31:0]         in_addr_i,
  input  logic [63:0]         in_rdata_i,
  input  logic                in_err_i,
  input  logic                in_rdata_align64_i,

  // output port
  output logic [1:0]          out_valid_o,
  input  logic [1:0]          out_ready_i,
  output ir_reg_t             out_instr0_o, 
  output ir_reg_t             out_instr1_o,
  output logic [31:0]         out_instr1_pc_spec0_o,
  output logic [31:0]         out_instr1_pc_spec1_o
);

  localparam int unsigned DEPTH = NUM_REQS+1;

  // index 0 is used for output
  logic [DEPTH-1:0] [64:0]  rdata_d,   rdata_q;
  logic [DEPTH-1:0]         err_d,     err_q;
  logic [DEPTH-1:0]         valid_d,   valid_q;
  logic [DEPTH-1:0]         lowest_free_entry;
  logic [DEPTH-1:0]         valid_pushed, valid_popped;
  logic [DEPTH-1:0]         entry_en;

  logic                     pop_fifo;
  //logic                     err,   err_unaligned, err_plus2;

  logic [31:1]              instr_addr_next;
  logic [31:1]              instr_addr_d, instr_addr_q;
  logic [31:1]              instr_addrp2_q, instr_addrp4_q;
  logic                     instr_addr_en;
  logic                     unused_addr_in;

  logic [1:0]   instr_xfr;
  logic [7:0]   comp_flag;
  logic [1:0]   instr_addr16;
  logic [127:0] rdata128;
  logic [2:0]   addr16_incr0, addr16_incr1;
  logic [1:0]   out_is_comp;
  logic [31:0]  out_addr0;
  logic [31:0]  out_rdata0;
  logic [31:0]  out_addr1;
  logic [31:0]  out_rdata1;
  logic         rdata_align64;
  logic [1:0]   fetch_err;

  /////////////////
  // Output port //
  /////////////////
  assign out_instr0_o.insn    = out_rdata0;
  assign out_instr0_o.pc      = out_addr0;
  assign out_instr0_o.is_comp = out_is_comp[0];
  assign out_instr0_o.errs    = ir_errs_t'({4'h0, fetch_err[0]});

  assign out_instr0_o.ptaken  = 1'b0;
  assign out_instr0_o.ptarget = 32'h0;

  assign out_instr1_o.insn    = out_rdata1;
  assign out_instr1_o.pc      = out_addr1;
  assign out_instr1_o.is_comp = out_is_comp[1];
  assign out_instr1_o.errs    = ir_errs_t'({4'h0, fetch_err[1]});

  assign out_instr1_o.ptaken  = 1'b0;
  assign out_instr1_o.ptarget = 32'h0;


  // QQQ fix this later
  // If entry[1] is valid, an error can come from entry[0] or entry[1], unless the
  // instruction in entry[0] is compressed (entry[1] is a new instruction)
  // If entry[1] is not valid, and entry[0] is, an error can come from entry[0] or the incoming
  // data, unless the instruction in entry[0] is compressed
  // If entry[0] is not valid, the error must come from the incoming data

  // assign err_unaligned   = valid_q[1] ? ((err_q[1] & ~unaligned_comp_flag) | err_q[0]) :
  //                                      ((valid_q[0] & err_q[0]) |
  //                                       (in_err_i & (~valid_q[0] | ~unaligned_comp_flag)));

  // Record when an error is caused by the second half of an unaligned 32bit instruction.
  // Only needs to be correct when unaligned and if err_unaligned is set
  // assign err_plus2       = valid_q[1] ? (err_q[1] & ~err_q[0]) :
  //                                      (in_err_i & valid_q[0] & ~err_q[0]);

  ////////////////////////////////////////
  // Instruction aligner (if unaligned) //
  ////////////////////////////////////////
  
  for (genvar i = 0; i < 8; i++) begin : gen_comp_flag
    assign comp_flag[i]   = (rdata128[i*16+:2] != 2'b11);
  end

  // rdata 128 can be either
  // {dont_care,  in_rdata_i}, if valid_q[0] == 0, in_valid_i == 1
  // {in_rdata_i, data_q[0]},  if valid_q[0] == 1, valid_q[1] == 0, in_valid_i == 1
  // {data_q[1],  data_q[0]},  if valid_q[0] == 1, valid_q[1] == 1
  // -- note valid_q[1] == 1 implies valid_q[0] == 1
  assign rdata128[63:0]   = valid_q[0] ? rdata_q[0][63:0] : in_rdata_i[63:0];
  assign rdata128[127:64] = valid_q[1] ? rdata_q[1][63:0] : in_rdata_i[63:0];

  assign rdata_align64   = valid_q[0] ? rdata_q[0][64] : in_rdata_align64_i;
  assign instr_addr16    = (UnalignedFetch && ~rdata_align64) ? {~instr_addr_q[2], instr_addr_q[1]} : instr_addr_q[2:1];

  assign instr_xfr = out_valid_o & out_ready_i;

  logic first_word_err, second_word_err;

  always_comb begin

    // after 1st word err, delination is lost so we really only need to send one instruction out 
    // so that the EX stages can trap properly.
    first_word_err  = 0;
    second_word_err = 0;

    // QQQ note we don't completely handle fetch_err for unalignedFetch case here yet
    if ((~in_valid_i & ~valid_q[1] & valid_q[0]) | (in_valid_i & ~valid_q[0])) begin   // 1 entry available
      first_word_err = (~valid_q[0] & in_err_i) || (valid_q[0] & err_q[0]);

      if (first_word_err) 
        out_valid_o = 2'b01;
      else if (instr_addr16 == 2'h0) 
        out_valid_o = 2'b11;
      else if ((instr_addr16 == 2'h1) && (comp_flag[1] | comp_flag[3])) 
        out_valid_o = 2'b11;
      else if (instr_addr16 == 2'h1) 
        out_valid_o = 2'b01;
      else if ((instr_addr16 == 2'h2) && comp_flag[2] && comp_flag[3]) 
        out_valid_o = 2'b11;
      else if (instr_addr16 == 2'h2)
        out_valid_o = 2'b01;
      else if ((instr_addr16 == 2'h3) && comp_flag[3]) 
        out_valid_o = 2'b01;
      else 
        out_valid_o = 2'b00;

      if (first_word_err) 
        fetch_err = 2'b01;
      else
        fetch_err = 2'b00;

    end else if ((in_valid_i & valid_q[0]) | valid_q[1]) begin       // more than 1 entry available
      first_word_err  = err_q[0];
      second_word_err = valid_q[1] ? err_q[1] : in_err_i;

      out_valid_o = 2'b11;

      if (first_word_err) 
        fetch_err  = 2'b11;
      else if (second_word_err && (instr_addr16 == 2'h3) && ~comp_flag[3])
        fetch_err = 2'b01;   // 32-bit instruction stradles word boundary
      else
        fetch_err = 2'b00;
    end else begin
      out_valid_o = 2'b00;
      fetch_err   = 2'b00;
    end

    if (instr_addr16 == 2'h0) begin
      out_rdata0 = rdata128[31:0];
      out_rdata1 = comp_flag[0] ? rdata128[47:16] : rdata128[63:32]; 
      out_is_comp   = {(comp_flag[0] ? comp_flag[1] : comp_flag[2]), comp_flag[0]};
    end else if (instr_addr16 == 2'h1) begin
      out_rdata0 = rdata128[47:16];
      out_rdata1 = comp_flag[1] ? rdata128[63:32] : rdata128[79:48];
      out_is_comp   = {(comp_flag[1] ? comp_flag[2] : comp_flag[3]), comp_flag[1]};
    end else if (instr_addr16 == 2'h2) begin
      out_rdata0 = rdata128[63:32];
      out_rdata1 = comp_flag[2] ? rdata128[79:48] : rdata128[95:64];
      out_is_comp   = {(comp_flag[2] ? comp_flag[3] : comp_flag[4]), comp_flag[2]};
    end else begin
      out_rdata0 = rdata128[79:48];
      out_rdata1 = comp_flag[3] ? rdata128[95:64] : rdata128[111:80];
      out_is_comp   = {(comp_flag[3] ? comp_flag[4] : comp_flag[5]), comp_flag[3]};
    end

    // only increase outgoing pc if instruction transferred (valid & ready)
    if ((instr_xfr == 2'b01) && out_is_comp[0]) begin
      addr16_incr0 = 1;
      pop_fifo    = (instr_addr16 == 2'h3);
    end else if (((instr_xfr == 2'b01) && ~out_is_comp[0]) || ((instr_xfr == 2'b11) && (out_is_comp == 2'b11))) begin
      addr16_incr0 = 2;
      pop_fifo    = (instr_addr16 == 2'h2) || (instr_addr16 == 2'h3);
    end else if ((instr_xfr == 2'b11) && (out_is_comp == 2'b00)) begin
      addr16_incr0 = 4;
      pop_fifo    = 1'b1;
    end else if (instr_xfr == 2'b11) begin
      addr16_incr0 = 3;
      pop_fifo    = (instr_addr16 != 2'h0);
    end else begin
      addr16_incr0 = 0;
      pop_fifo    = 1'b0;
    end
  end

  /////////////////////////
  // Instruction address //
  /////////////////////////

  // Update the address on branches and every time either 1 or 2 instruction is driven 
  assign instr_addr_en = clear_i | (|(out_ready_i & out_valid_o)); 

  // Increment the address by two every time a compressed instruction is popped
  assign instr_addr_next = instr_addr_q[31:1] + addr16_incr0;

  assign instr_addr_d = clear_i ? in_addr_i[31:1] : instr_addr_next;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_addr_q   <= '0;
    end else if (instr_addr_en) begin
      instr_addr_q   <= instr_addr_d;
    end
  end

  // parallelizing/precompute adders to help timing a bit..
  logic [31:1] instr_addrp2_d, instr_addrp4_d;
  assign instr_addrp2_d = clear_i ? (in_addr_i[31:1] + 1) : (instr_addr_next + 1);
  assign instr_addrp4_d = clear_i ? (in_addr_i[31:1] + 2) : (instr_addr_next + 2);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_addrp2_q <= '0;
      instr_addrp4_q <= '0;
    end else if (instr_addr_en) begin
      instr_addrp2_q <= instr_addrp2_d;
      instr_addrp4_q <= instr_addrp4_d;
    end
  end

  // Output PC of current instruction
  assign out_addr0  = {instr_addr_q, 1'b0};
  assign out_addr1  = {(out_is_comp[0] ? instr_addrp2_q : instr_addrp4_q), 1'b0} ;

  assign out_instr1_pc_spec0_o = {instr_addrp2_q, 1'b0};
  assign out_instr1_pc_spec1_o = {instr_addrp4_q, 1'b0};

  // The LSB of the address is unused, since all addresses are halfword aligned
  assign unused_addr_in = in_addr_i[0];

  /////////////////
  // FIFO status //
  /////////////////

  // Indicate the fill level of fifo-entries. This is used to determine when a new request can be
  // made on the bus. The prefetch buffer only needs to know about the upper entries which overlap
  // with NUM_REQS.
  assign busy_o = valid_q[DEPTH-1:DEPTH-NUM_REQS];

  /////////////////////
  // FIFO management //
  /////////////////////

  // Since an entry can contain unaligned instructions, popping an entry can leave the entry valid
  //assign pop_fifo = out_ready_i & out_valid_o & (~aligned_comp_flag | out_addr_o[1]); 

  for (genvar i = 0; i < (DEPTH - 1); i++) begin : g_fifo_next
    // Calculate lowest free entry (write pointer)
    if (i == 0) begin : g_ent0
      assign lowest_free_entry[i] = ~valid_q[i];
    end else begin : g_ent_others
      assign lowest_free_entry[i] = ~valid_q[i] & valid_q[i-1];
    end

    // An entry is set when an incoming request chooses the lowest available entry
    assign valid_pushed[i] = (in_valid_i & lowest_free_entry[i]) |
                             valid_q[i];
    // Popping the FIFO shifts all entries down
    assign valid_popped[i] = pop_fifo ? valid_pushed[i+1] : valid_pushed[i];
    // All entries are wiped out on a clear
    assign valid_d[i] = valid_popped[i] & ~clear_i;

    // data flops are enabled if there is new data to shift into it, or
    assign entry_en[i] = (valid_pushed[i+1] & pop_fifo) |
                         // a new request is incoming and this is the lowest free entry
                         (in_valid_i & lowest_free_entry[i] & ~pop_fifo);

    // take the next entry or the incoming data
    assign rdata_d[i]  = valid_q[i+1] ? rdata_q[i+1] : {in_rdata_align64_i, in_rdata_i};
    assign err_d  [i]  = valid_q[i+1] ? err_q  [i+1] : in_err_i;
  end

  // The top entry is similar but with simpler muxing
  assign lowest_free_entry[DEPTH-1] = ~valid_q[DEPTH-1] & valid_q[DEPTH-2];
  assign valid_pushed     [DEPTH-1] = valid_q[DEPTH-1] | (in_valid_i & lowest_free_entry[DEPTH-1]);
  assign valid_popped     [DEPTH-1] = pop_fifo ? 1'b0 : valid_pushed[DEPTH-1];
  assign valid_d [DEPTH-1]          = valid_popped[DEPTH-1] & ~clear_i;
  assign entry_en[DEPTH-1]          = in_valid_i & lowest_free_entry[DEPTH-1];
  assign rdata_d [DEPTH-1]          = {in_rdata_align64_i, in_rdata_i};
  assign err_d   [DEPTH-1]          = in_err_i;

  ////////////////////
  // FIFO registers //
  ////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= '0;
    end else begin
      valid_q <= valid_d;
    end
  end

  for (genvar i = 0; i < DEPTH; i++) begin : g_fifo_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rdata_q[i] <= '0;
        err_q[i]   <= '0;
      end else if (entry_en[i]) begin
        rdata_q[i] <= rdata_d[i];
        err_q[i]   <= err_d[i];
      end
    end
  end

endmodule
