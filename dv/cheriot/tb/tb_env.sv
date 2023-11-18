// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
`timescale 1ns/1ps

module tb_env;

  logic         clk;
  logic         rst_n;
  logic [31:0]  instr_rdata_dii, nxt_instr;
  logic [31:0]  instr_pc;
  logic         instr_ack;

  tb_cheriot_top u_tb_top (
    .clk_i             (clk),
    .rstn_i            (rst_n),
    .instr_rdata_dii_i (instr_rdata_dii),
    .instr_pc_o        (instr_pc),
    .instr_ack_o       (instr_ack)
  );


  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #5 clk = ~clk;
    end
  end

 
`ifdef DII_SIM

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      instr_rdata_dii <= 32'h1;
    end else begin
      instr_rdata_dii <= nxt_instr;      // select between possible nxt_instr streams 
    end
  end

  // Uses a stream file instead of a socket for now (easier for VCS)
  logic [31:0] instr_stream[0:65535];

  initial begin
    int unsigned cnt;
    logic        eof;

    cnt = 0;
    eof = 0;

    rst_n = 1'b1;
    #1;
    rst_n = 1'b0;
   
    $readmemh("./bin/instr_stream.vhx", instr_stream, 'h0);   // load stream 
    nxt_instr = instr_stream[0];

    repeat(10) @(posedge clk);
    #1;
    rst_n = 1'b1;

    while (!eof) begin
      @(posedge clk);
      if (instr_ack) begin
        cnt++;
        nxt_instr = instr_stream[cnt];
        if (nxt_instr[0]  === 1'bx) begin
          nxt_instr = 32'h1;          // NOP
          eof = 1'b1;
        end
      end
    end

    repeat(10) @(posedge clk); // let the last instruction propagate through
    
    $finish;
  end

`else           // execute from ELF image (in the instruction memory)
  assign instr_rdata_dii = 32'h0;

  initial begin
    bit cont_flag;
    int i;

    rst_n = 1'b1;
    #1;
    rst_n = 1'b0;

    // overlaying the same image in both instr_mem model and data_mem model
    // so that we can get RO data. this works in this setup since we only use static code images. 
    $readmemh("./bin/instr_mem.vhx", u_tb_top.u_instr_mem.mem, 'h0);   // load main executable
    $readmemh("./bin/instr_mem.vhx", u_tb_top.u_data_mem.mem, 'h0);   // load main executable

    //for (i=0; i<64;i++)
    //  $display("%08x %08x %08x %08x", u_tb_top.u_instr_mem.mem[4*i], u_tb_top.u_instr_mem.mem[4*i+1],
    //                                  u_tb_top.u_instr_mem.mem[4*i+2], u_tb_top.u_instr_mem.mem[4*i+3]);
   
    
    repeat(10) @(posedge clk);
    rst_n = 1'b1;
    
    cont_flag = 1;
    while (cont_flag) begin
      @(posedge clk);
      if (u_tb_top.data_req & u_tb_top.data_gnt & (u_tb_top.data_addr == 32'h80040200)) begin
        if (u_tb_top.data_wdata[7])
          cont_flag = 0;
        else
          $write("%c", u_tb_top.data_wdata[7:0]);
      end
    end

    repeat(10) @(posedge clk);
    $finish;

  end

`endif

endmodule
