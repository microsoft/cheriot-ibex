// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

module tb_env;

  logic         clk;
  logic         rst_n;
  logic [31:0]  dii_insn, nxt_instr;
  logic [31:0]  dii_pc;
  logic         dii_ack;

  tb_cheriot_top u_tb_top (
    .clk_i      (clk),
    .rstn_i     (rst_n),
    .dii_insn_i (dii_insn),
    .dii_pc_o   (dii_pc),
    .dii_ack_o  (dii_ack)
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
      dii_insn <= 32'h1;
    end else begin
      dii_insn <= nxt_instr;      // select between possible nxt_instr streams 
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
      if (dii_ack) begin
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
  assign dii_insn = 32'h0;

  string test_name, vhx_path;

  initial begin
    bit cont_flag;
    int i;

    i = $value$plusargs("TEST=%s", test_name);
    if (i == 0)
      $sformat(test_name, "hello_world");

    $sformat(vhx_path, "./bin/%s.vhx", test_name);
    $display("Loading test %s", test_name);

    rst_n = 1'b1;
    #1;
    rst_n = 1'b0;

    // overlaying the same image in both instr_mem model and data_mem model
    // so that we can get RO data. this works in this setup since we only use static code images. 
    $readmemh(vhx_path, u_tb_top.u_instr_mem.iram, 'h0);   // load main executable
    $readmemh(vhx_path, u_tb_top.u_data_mem.dram, 'h0);   // load main executable

    //for (i=0; i<64;i++)
    //  $display("%08x %08x %08x %08x", u_tb_top.u_instr_mem.mem[4*i], u_tb_top.u_instr_mem.mem[4*i+1],
    //                                  u_tb_top.u_instr_mem.mem[4*i+2], u_tb_top.u_instr_mem.mem[4*i+3]);
   
    
    repeat(10) @(posedge clk);
    rst_n = 1'b1;
    
    cont_flag = 1;
    while (cont_flag) begin
      @(posedge clk);
      if (u_tb_top.data_req & u_tb_top.data_gnt & (u_tb_top.data_addr == 32'h83800200)) begin
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
