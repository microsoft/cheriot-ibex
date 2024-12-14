// Copyright (C) Microsoft Corporation. All rights reserved.


`include "dvp_ibex_defines.svh"

module ibex_memory (

  input             clk_i,
  input             rstn_i,

  input             IROM_EN_i,
  input  [31:0]     IROM_ADDR_i,
  output [32:0]     IROM_RDATA_o,
  output            IROM_READY_o,
  output            IROM_ERROR_o,
  input             IROM_WE_i,
  input  [3:0]      IROM_BE_i,
  input  [32:0]     IROM_WDATA_i,

  input             IRAM_EN_i,
  input  [31:0]     IRAM_ADDR_i,
  input  [32:0]     IRAM_WDATA_i,
  input             IRAM_WE_i,
  input  [3:0]      IRAM_BE_i,
  output [32:0]     IRAM_RDATA_o,
  output            IRAM_READY_o,
  output            IRAM_ERROR_o,

  input             DRAM_EN_i,
  input  [31:0]     DRAM_ADDR_i,
  input  [32:0]     DRAM_WDATA_i,
  input             DRAM_WE_i,
  input  [3:0]      DRAM_BE_i,
  output [32:0]     DRAM_RDATA_o,
  output            DRAM_READY_o,
  output            DRAM_ERROR_o,
 
  input             tsmap_cs_i,
  input  [15:0]     tsmap_addr_i,
  output [31:0]     tsmap_rdata_o,

  input             dma_tsmap_cs_i,
  input  [15:0]     dma_tsmap_addr_i,
  output [31:0]     dma_tsmap_rdata_o,
  output            tsmap_is_occupied_o,

  output logic         snooped_tsmap_cs_o,
  output logic [15:0]  snooped_tsmap_addr_o,
  output logic [31:0]  snooped_tsmap_rdata_o

);


//===============================================
// Internal Wires
//===============================================
wire        clk;
wire        rstn;

wire        IROM_EN;
wire [31:0] IROM_ADDR;
wire [32:0] IROM_WDATA;
wire        IROM_WE;
wire [3:0]  IROM_BE;
wire [32:0] IROM_RDATA;

wire        irom_wren;

wire        IRAM_EN;
wire [31:0] IRAM_ADDR;
wire [32:0] IRAM_WDATA;
wire        IRAM_WE;
wire [3:0]  IRAM_BE;
wire [32:0] IRAM_RDATA;
wire        IRAM_READY;
wire        IRAM_ERROR;

wire        DRAM_EN;
wire [31:0] DRAM_ADDR;
wire [32:0] DRAM_WDATA;
wire        DRAM_WE;
wire [3:0]  DRAM_BE;
wire [32:0] DRAM_RDATA;
wire        DRAM_READY;
wire        DRAM_ERROR;

//===============================================
// IROM
//===============================================
//fpga_block_ram_model_dvp #(
fpga_block_ram_byte_wr_model_dvp #(
    .RAM_WIDTH (33),
    .RAM_DEPTH ('h10000),
    .INIT_FILE (`DVP_IROM_INIT_FILE)
  ) irom (
    .clk    (clk),
    .cs     (IROM_EN),
    .dout   (IROM_RDATA),
    .addr   (IROM_ADDR[17:2]),
    .din    (IROM_WDATA),
    .we     (IROM_WE & irom_wren),
    .wstrb({ 1'b1, {8{IROM_BE[3]}}, {8{IROM_BE[2]}}, {8{IROM_BE[1]}}, {8{IROM_BE[0]}} }),
    .ready  ()
  );
    
//===============================================
// IRAM
//===============================================
fpga_block_ram_byte_wr_model_dvp #(
    .RAM_WIDTH        (33),
    .RAM_DEPTH        ('h20000),
    .INIT_FILE        ("")
  ) iram (
    .clk    (clk),
    .cs     (IRAM_EN),
    .addr   (IRAM_ADDR[18:2]),
    .dout   (IRAM_RDATA),
    .din    (IRAM_WDATA),
    .we     (IRAM_WE),
    .wstrb({ 1'b1, {8{IRAM_BE[3]}}, {8{IRAM_BE[2]}}, {8{IRAM_BE[1]}}, {8{IRAM_BE[0]}} }),
    .ready  (IRAM_READY)
  );

//===============================================
// DRAM
//===============================================

//===============================================
// Alternative 1 for safety at DMA controller
//===============================================

logic            tsmap_cs;
logic [15:0]     tsmap_addr, tsmap_addr_reg;
logic [31:0]     tsmap_rdata;

logic tsmap_is_occupied;
logic dma_tsmap_is_occupied;

assign tsmap_cs = tsmap_cs_i || dma_tsmap_cs_i;
// cpu requests are always in the priority
assign tsmap_addr = tsmap_cs_i ? tsmap_addr_i : dma_tsmap_addr_i;

// we are assuming that the result is available 
// in the next cycle for the cpu
assign tsmap_is_occupied_o = tsmap_cs_i;

// only the accurate should pass through,
// unless otherwise only 0
assign tsmap_rdata_o     = tsmap_is_occupied ? tsmap_rdata : 0;
assign dma_tsmap_rdata_o = dma_tsmap_is_occupied ? tsmap_rdata : 0;

//===============================================
// Alternative 2 for safety at DMA controller.
// Everything but the rdata are the delayed signals
// to keep the logic at the DMA simpler
//===============================================
assign snooped_tsmap_cs_o = tsmap_is_occupied;
assign snooped_tsmap_addr_o = tsmap_addr_i;
assign snooped_tsmap_rdata_o = tsmap_rdata;

always_ff @( posedge clk ) begin : assigning_Tsmap_Inp
  if (!rstn) begin
    tsmap_is_occupied     <= 0;
    dma_tsmap_is_occupied <= 0;
    tsmap_addr_reg <= 0;
  end else begin
    tsmap_is_occupied     <= tsmap_cs_i;
    dma_tsmap_is_occupied <= (!tsmap_cs_i & dma_tsmap_cs_i);
    tsmap_addr_reg        <= tsmap_addr_i;
  end
end

fpga_block_ram_2port_model_dvp #(
    .RAM_WIDTH        (33),
    .RAM_DEPTH        ('h4000),
    .INIT_FILE        ("")
  ) dram (
    .clk(clk),
    .cs(DRAM_EN),
    .dout(DRAM_RDATA),
    .addr(DRAM_ADDR[15:2]),
    .din(DRAM_WDATA),
    .we(DRAM_WE),
    .wstrb({ 1'b1, {8{DRAM_BE[3]}}, {8{DRAM_BE[2]}}, {8{DRAM_BE[1]}}, {8{DRAM_BE[0]}} }),
    .ready(dram_rdy),
    .cs2  (tsmap_cs),
    .addr2(tsmap_addr[12:0]),
    .dout2(tsmap_rdata)
  );

//===============================================
// Connect ports
//===============================================
assign clk = clk_i;
assign rstn = rstn_i;

assign IROM_EN = IROM_EN_i;
assign IROM_ADDR = IROM_ADDR_i;
assign IROM_RDATA_o = IROM_RDATA;
assign IROM_READY_o = 1'b1;
assign IROM_ERROR_o = 1'b0;
assign IROM_WDATA = IROM_WDATA_i;
assign IROM_WE = IROM_WE_i;
assign IROM_BE = IROM_BE_i;

assign IRAM_EN = IRAM_EN_i;
assign IRAM_ADDR = IRAM_ADDR_i;
assign IRAM_WDATA = IRAM_WDATA_i;
assign IRAM_WE = IRAM_WE_i;
assign IRAM_BE = IRAM_BE_i;
assign IRAM_RDATA_o = IRAM_RDATA;
assign IRAM_READY_o = 1'b1;
assign IRAM_ERROR_o = 1'b0;

assign DRAM_EN = DRAM_EN_i;
assign DRAM_ADDR = DRAM_ADDR_i;
assign DRAM_WDATA = DRAM_WDATA_i;
assign DRAM_WE = DRAM_WE_i;
assign DRAM_BE = DRAM_BE_i;
assign DRAM_RDATA_o = DRAM_RDATA;
assign DRAM_READY_o = 1'b1;
assign DRAM_ERROR_o = 1'b0;

endmodule 
