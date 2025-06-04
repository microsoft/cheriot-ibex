// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// instr interface/memory model
//
module instr_mem_model # (
  parameter bit UnalignedFetch = 1'b1
) ( 
  input  logic        clk,
  input  logic        rst_n,

  input  logic [2:0]  ERR_RATE,    
  input  logic [3:0]  GNT_WMAX,
  input  logic [3:0]  RESP_WMAX,
  input  logic        err_enable,

  input  logic        instr_req,
  input  logic [31:0] instr_addr,

  output logic        instr_gnt,
  output logic        instr_rvalid,
  output logic [63:0] instr_rdata,
  output logic        instr_err
);
  localparam int unsigned MEM_AW     = 15;   // use the higher 256kB for debug ROM space 
  localparam int unsigned MEM_DW     = 64; 
 
  logic              mem_cs;
  logic [MEM_DW-1:0] mem_din;
  logic [MEM_DW-1:0] mem_rdata;
  logic [29:0]       mem_addr32;

  logic [MEM_AW-1:0] iram_addr;
  logic              iram_err, iram_err_q;

  // simple unified memory system model
  reg   [MEM_DW-1:0] iram[0:2**MEM_AW-1];

  mem_obi_if #(
    .DW         (MEM_DW),
    .sample_delay (2)
  ) u_mem_obj_if (
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .GNT_WMAX     (GNT_WMAX),
    .RESP_WMAX    (RESP_WMAX),
    .data_req     (instr_req),
    .data_we      (1'b0),
    .data_be      (4'hf),
    .data_is_cap  (1'b0),
    .data_addr    (instr_addr),
    .data_wdata   (64'h0),
    .data_flag    (8'h0),
    .data_gnt     (instr_gnt),
    .data_rvalid  (instr_rvalid),
    .data_rdata   (instr_rdata),
    .data_err     (instr_err),
    .data_resp_info (),
    .mem_cs       (mem_cs),
    .mem_is_cap   (),
    .mem_we       (),
    .mem_be       (),
    .mem_flag     (),
    .mem_addr32   (mem_addr32),
    .mem_wdata    (),
    .mem_rdata    (mem_rdata),
    .mem_err      (iram_err)
  );
 
  //
  // memory signals (sampled @posedge clk)
  //

  assign iram_addr = mem_addr32[MEM_AW:1];

  if (UnalignedFetch) begin
    always @(posedge clk) begin
      if (mem_cs && ~mem_addr32[0])
        mem_rdata <= iram[iram_addr];  
      else if (mem_cs)
        mem_rdata <= {iram[iram_addr+1][31:0], iram[iram_addr][63:32]};
    end
  end else begin
    always @(posedge clk) begin
      if (mem_cs)
        mem_rdata <= iram[iram_addr];  
    end
  end

  localparam logic [31:0] err_keepout_base = 32'h8000_0000;
  localparam logic [31:0] err_keepout_top  = 32'h8000_01ff;

  assign iram_err = iram_err_q && ((mem_addr32 < err_keepout_base[31:2]) || 
                                   (mem_addr32 > err_keepout_top[31:2]));

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      iram_err_q    <= 1'b0;
    end else begin
      if (~err_enable)
        iram_err_q    <= 1'b0;
      else if (mem_cs)
        iram_err_q <=  (ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-ERR_RATE))==0);

    end
  end 
 
  // initialize debug ROM content
//  initial begin
//    #1;
//    // debug entry
//    iram[65536] = 32'h0001_0001;   // nop, nop
//    iram[65537] = 32'h7b20_0073;   // dret
//    iram[65538] = 32'h0;
//   
//    // debug mode exception handler 
//    iram[65568] = 32'h0001_0001;
//    iram[65569] = 32'h3020_0073;   // mret
//    iram[65570] = 32'h0;
//  end

endmodule
