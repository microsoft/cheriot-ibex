// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// data interface/memory model
//
module data_mem_model import cheriot_dv_pkg::*; ( 
  input  logic              clk,
  input  logic              rst_n,

  input  logic              data_req,
  input  logic              data_we,
  input  logic [3:0]        data_be,
  input  logic              data_is_cap,
  input  logic [31:0]       data_addr,
  input  logic [32:0]       data_wdata,
  input  logic [7:0]        data_flag,

  output logic              data_gnt,
  output logic              data_rvalid,
  output logic [32:0]       data_rdata,
  output logic              data_err,

  input  logic              tsmap_cs,
  input  logic [15:0]       tsmap_addr,
  output logic [31:0]       tsmap_rdata
);
 
  localparam int unsigned DRAM_AW     = 21; 

  logic        mem_cs;
  logic        mem_we;
  logic [3:0]  mem_be;
  logic [29:0] mem_addr32;
  logic [32:0] mem_wdata;
  logic [32:0] mem_rdata;
  logic        mem_err;

  // simple unified memory system model
  logic [32:0]        dram[0:2**DRAM_AW-1];
  logic [DRAM_AW-1:0] dram_addr32;
  logic [32:0]        dram_rdata;
  logic               dram_sel, dram_cs;
  logic               dram_err_schd;

  mem_obi_if #(
    .DW         (33)
  ) u_mem_obj_if (
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .GNT_WMAX     (4'h2),
    .RESP_WMAX    (4'h2),
    .data_req     (data_req),
    .data_we      (data_we),
    .data_be      (data_be),
    .data_is_cap  (data_is_cap),
    .data_addr    (data_addr),
    .data_wdata   (data_wdata),
    .data_flag    (8'h0),
    .data_gnt     (data_gnt),
    .data_rvalid  (data_rvalid),
    .data_rdata   (data_rdata),
    .data_err     (data_err),
    .data_resp_info (),
    .mem_cs       (mem_cs),
    .mem_we       (mem_we),
    .mem_be       (mem_be),
    .mem_flag     (),
    .mem_addr32   (mem_addr32),
    .mem_wdata    (mem_wdata),
    .mem_rdata    (mem_rdata),
    .mem_err      (mem_err)
  );

  //
  // memory signals (sampled @posedge clk)
  //
  logic dram_sel_q;

  assign mem_rdata = dram_sel_q ? dram_rdata : 0;
  assign mem_err = mem_cs & !dram_sel;

  //
  // DRAM (data RAM or rv_ram per sail)
  // starting at 0x8000_0000, size 0x80_0000 
  //   note in sail rv_ram size for RVFI_DII is smaller than the ELF case
  //
  // don't generate memory access if
  //   - responds with an error, or
  //   - accesses from stkz is supposed to be ignored.
  assign dram_addr32 = mem_addr32[DRAM_AW-1:0];
  assign dram_sel    = mem_cs & mem_addr32[29] & (mem_addr32[28:DRAM_AW] == 0);   
  assign dram_cs     = dram_sel;   

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      dram_sel_q      <= 1'b0;
    end else begin
      dram_sel_q      <= dram_sel;
    end
  end

  always @(posedge clk) begin
    if (dram_cs && mem_we) begin
      if(mem_be[0])
        dram[dram_addr32][7:0]  <= mem_wdata[7:0];
      if(mem_be[1])
        dram[dram_addr32][15:8] <= mem_wdata[15:8];
      if(mem_be[2])
        dram[dram_addr32][23:16] <= mem_wdata[23:16];
      if(mem_be[3])
        dram[dram_addr32][31:24] <= mem_wdata[31:24];

      // valid tag bit for caps - only allow to update for word accesses, where bit[32] is taken 
      // care of by CPU, otherwise clear the valid bit.
      //  - if the physical memory doesn't support BE for bit[32], then needs RMW or 
      //    separate mem for tag bits..
       // - only makes sure data accesses can't modify capabilities but could still read..
      // is this sufficent for cheri - QQQ? 
      //  - the original cheri ask is to qualify memory accesses based on the tag bit, which requires RMW
      if (|mem_be)  dram[dram_addr32][32]  <= mem_wdata[32];
        
    end else if (dram_cs)
      dram_rdata <= dram[dram_addr32];  
  end

  // TSMAP RAM is part of the DRAM space with an independent read port
  logic [DRAM_AW-1:0] tsram_addr32;

  assign tsram_addr32 = 24'hc0_0000 + tsmap_addr;  // base address 0x8300_0000
 
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      tsmap_rdata <= 32'h0;
    end else if (dram_cs) begin
      tsmap_rdata <= dram[tsram_addr32];  
    end
  end

  // initialize memory content to match sail
  initial begin 
     int i;
     while (1) begin
       @(posedge rst_n);
       for (i=0; i < 2**DRAM_AW; i++) dram[i] = 33'h0;
     end
  end 
  
endmodule
