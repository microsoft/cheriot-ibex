// Copyright (C) Microsoft Corporation. All rights reserved.

// Parameters
// SIZE   4K = 12
// SIZE   8K = 13
// SIZE  16K = 14
// SIZE  32K = 15
// SIZE  64K = 16
// SIZE 128K = 17
// SIZE 256K = 18
// SIZE 512K = 19


// 
//    Master side mux
//

module mstr_mux # (
  parameter DBGMEM_START_ADDRESS = 32'h0000_0000,
  parameter DBGMEM_END_ADDRESS   = 32'h0300_0000,
  parameter IROM_START_ADDRESS   = 32'h2000_0000,
  parameter IROM_END_ADDRESS     = 32'h2004_0000,
  parameter IRAM_START_ADDRESS   = 32'h2004_0000,
  parameter IRAM_END_ADDRESS     = 32'h200C_0000,
  parameter DRAM_START_ADDRESS   = 32'h200F_0000,
  parameter DRAM_END_ADDRESS     = 32'h2010_0000,
  parameter DMA_START_ADDRESS    = 32'h2020_0000,
  parameter DMA_END_ADDRESS      = 32'h2020_0040,
  parameter nSLV                 = 6
  ) (
  input  logic                  clk_i,
  input  logic                  rstn_i,

  // master side signals
  input  logic                  mstr_req_i,
  output logic                  mstr_gnt_o,
  input  logic [31:0]           mstr_addr_i,
  input  logic [3:0]            mstr_be_i,
  input  logic [32:0]           mstr_wdata_i, 
  input  logic                  mstr_we_i, 
  output logic [32:0]           mstr_rdata_o, 
  output logic                  mstr_rvalid_o,
  output logic                  mstr_err_o,
                               
  output logic [nSLV-1:0]       slv_req_o,
  output logic [31:0]           slv_addr_o,
  output logic [3:0]            slv_be_o,
  output logic [32:0]           slv_wdata_o, 
  output logic                  slv_we_o, 
  input  logic [nSLV-1:0]       slv_gnt_i,
  
  input  logic [nSLV-1:0][32:0] slv_rdata_i, 
  input  logic [nSLV-1:0]       slv_rvalid_i,
  input  logic [nSLV-1:0]       slv_err_i
  
);
 
`define IS_DBG_IROM_ADDR(addr)   (addr >= DBGMEM_START_ADDRESS && addr < DBGMEM_END_ADDRESS)
`define IS_IROM_ADDR(addr)       (addr >= IROM_START_ADDRESS && addr < IROM_END_ADDRESS) 
`define IS_IRAM_ADDR(addr)       (addr >= IRAM_START_ADDRESS && addr < IRAM_END_ADDRESS)
`define IS_DRAM_ADDR(addr)       (addr >= DRAM_START_ADDRESS && addr < DRAM_END_ADDRESS)
`define IS_DMA_ADDR(addr)        (addr >= DMA_START_ADDRESS && addr < DMA_END_ADDRESS)

  logic [nSLV-1:0] pending_slv_resp;
  logic [nSLV-1:0] slv_req_dec;
  logic            mstr_gnt;
  logic            rvalid_done, rvalid_done_q;

  assign mstr_gnt_o = mstr_gnt;

  assign mstr_gnt = |(slv_gnt_i & slv_req_o);  // hold off gnt till the actuall slv_req_o is generated

  // slv_req generation
  // if switching slaves, hold off req until the response from the previous slave is back to avoid conflicts
  //

  assign rvalid_done = ((pending_slv_resp & slv_rvalid_i) != 0);
  assign slv_req_o   = ((pending_slv_resp == 0) || (pending_slv_resp == slv_req_dec) || rvalid_done) ? slv_req_dec : 0;

  // pass through
  assign slv_addr_o   = mstr_addr_i;
  assign slv_be_o     = mstr_be_i;
  assign slv_we_o     = mstr_we_i;
  assign slv_wdata_o  = mstr_wdata_i;

  always @(posedge clk_i or negedge rstn_i)
  begin
    if(~rstn_i) begin
      pending_slv_resp  <= 0;
    end else begin
      if(mstr_gnt)          pending_slv_resp <= slv_req_dec;
      else if (rvalid_done) pending_slv_resp <= 0;
    end
  end

  //========================================
  // Address Space Defines
  //========================================

  always_comb begin
    int i;

    if (mstr_req_i && `IS_DBG_IROM_ADDR(mstr_addr_i))
      slv_req_dec = 'h1;
    else if (mstr_req_i && `IS_IROM_ADDR(mstr_addr_i))
      slv_req_dec = 'h2;
    else if (mstr_req_i && `IS_IRAM_ADDR(mstr_addr_i))
      slv_req_dec = 'h4;
    else if (mstr_req_i && `IS_DRAM_ADDR(mstr_addr_i))
      slv_req_dec = 'h8;
    else if (mstr_req_i && `IS_DMA_ADDR(mstr_addr_i))
      slv_req_dec = 'h20;
    else if (mstr_req_i)
      slv_req_dec = 'h10;           // default choose AXI
    else
      slv_req_dec = 'h0;

    mstr_rdata_o = 33'h0;
    for (i = 0; i < nSLV; i++) begin
      if (pending_slv_resp[i]) mstr_rdata_o = slv_rdata_i[i];
    end 
   
  end

  assign mstr_rvalid_o = |(pending_slv_resp & slv_rvalid_i);
  assign mstr_err_o    = |(pending_slv_resp & slv_err_i);

endmodule

// 
//   Slave side mux for TCM memories
//

module slv_mem_mux # (
  parameter nMSTR               = 4
  ) (
  input  logic                     clk_i,
  input  logic                     rstn_i,

  // master side signals
  input  logic [nMSTR-1:0]         mstr_req_i,
  output logic [nMSTR-1:0]         mstr_gnt_o,
  input  logic [nMSTR-1:0][31:0]   mstr_addr_i,
  input  logic [nMSTR-1:0][3:0]    mstr_be_i,
  input  logic [nMSTR-1:0][32:0]   mstr_wdata_i, 
  input  logic [nMSTR-1:0]         mstr_we_i, 
  output logic [32:0]              mstr_rdata_o, 
  output logic                     mstr_rvalid_o,
  output logic                     mstr_err_o,
                               
  output logic                     mem_en_o,
  output logic [31:0]              mem_addr_o,
  output logic [32:0]              mem_wdata_o,
  output logic                     mem_we_o,
  output logic [3:0]               mem_be_o,
  input  logic [32:0]              mem_rdata_i,
  input  logic                     mem_ready_i,
  input  logic                     mem_error_i
);

  logic [nMSTR-1:0] mstr_gnt;
  logic             rvalid;

  assign mstr_gnt_o    = mstr_gnt;
  assign mstr_rdata_o  = mem_rdata_i;
  assign mstr_rvalid_o = rvalid;            
  assign mstr_err_o    = mem_error_i;

  // gnt by strict priority assignment - mst_req[0] == highest priority
  for (genvar i = 0; i < nMSTR; i++) begin
    logic [7:0] pri_mask;
    assign pri_mask = 8'hff >> (8-i);      // max 8 masters, should be enough 
    assign mstr_gnt[i] = mem_ready_i & mstr_req_i[i] & ~(|(mstr_req_i & pri_mask));
  end

  // mux for mem side controls
  assign mem_en_o = |mstr_gnt;
  
  always_comb begin
    int i;

    mem_addr_o  = 32'h0;
    mem_wdata_o = 33'h0;
    mem_we_o    = 1'b0;
    mem_be_o    = 4'h0;

    for (i = 0; i < nMSTR; i++) begin
      mem_addr_o  = mem_addr_o  | (mstr_addr_i[i] & {32{mstr_gnt[i]}});
      mem_wdata_o = mem_wdata_o | (mstr_wdata_i[i] & {33{mstr_gnt[i]}});
      mem_we_o    = mem_we_o    | (mstr_we_i[i] & mstr_gnt[i]);
      mem_be_o    = mem_be_o    | (mstr_be_i[i] & {4{mstr_gnt[i]}});
    end 

  end

  always @(posedge clk_i or negedge rstn_i) begin
    if(~rstn_i) begin
      rvalid <= 1'b0;
    end else begin
      rvalid <= |mstr_gnt;
    end
  end

endmodule

// 
//   Slave side mux for the AXI bus
//

module slv_axi_mux # (
  parameter AXI_ID             = 4'h0,
  parameter USER_BIT_WIDTH     = 12,
  parameter nMSTR              = 4
  ) (
  input  logic                       clk_i,
  input  logic                       rstn_i,

  // master side signals
  input  logic [nMSTR-1:0]           mstr_req_i,
  output logic [nMSTR-1:0]           mstr_gnt_o,
  input  logic [nMSTR-1:0][31:0]     mstr_addr_i,
  input  logic [nMSTR-1:0][3:0]      mstr_be_i,
  input  logic [nMSTR-1:0][32:0]     mstr_wdata_i, 
  input  logic [nMSTR-1:0]           mstr_we_i, 
  output logic [32:0]                mstr_rdata_o, 
  output logic                       mstr_rvalid_o,
  output logic                       mstr_err_o,
                                     
  output logic [3:0]                 AWID_o,
  output logic [31:0]                AWADDR_o,
  output logic [7:0]                 AWLEN_o,
  output logic [2:0]                 AWSIZE_o,
  output logic [1:0]                 AWBURST_o,
  output logic [1:0]                 AWLOCK_o,
  output logic [2:0]                 AWPROT_o,
  output logic [3:0]                 AWCACHE_o,
  output logic [USER_BIT_WIDTH-1:0]  AWUSER_o,
  output logic                       AWVALID_o,
  input  logic                       AWREADY_i,

  output logic [31:0]                WDATA_o,
  output logic [3:0]                 WSTRB_o,
  output logic                       WLAST_o,
  output logic                       WVALID_o,
  input  logic                       WREADY_i,
                                    
  input  logic [3:0]                 BID_i,
  input  logic [1:0]                 BRESP_i,
  input  logic                       BVALID_i,
  output logic                       BREADY_o,
                                
  output logic [3:0]                 ARID_o,
  output logic [31:0]                ARADDR_o,
  output logic [7:0]                 ARLEN_o,
  output logic [2:0]                 ARSIZE_o,
  output logic [1:0]                 ARBURST_o,
  output logic [1:0]                 ARLOCK_o,
  output logic [2:0]                 ARPROT_o,
  output logic [3:0]                 ARCACHE_o,
  output logic [USER_BIT_WIDTH-1:0]  ARUSER_o,
  output logic                       ARVALID_o,
  input  logic                       ARREADY_i,
                                 
  input  logic [3:0]                 RID_i,
  input  logic [31:0]                RDATA_i,
  input  logic                       RLAST_i,
  input  logic [1:0]                 RRESP_i,
  input  logic                       RVALID_i,
  output logic                       RREADY_o
);

  typedef enum {AXI_IDLE, AXI_ACC, AXI_RESP} axi_fsm_t;

  axi_fsm_t axi_fsm_q;     

  logic [nMSTR-1:0] mstr_gnt, mstr_gnt_q;
  logic             axi_wr_done, w_done, aw_done;
  logic             axi_acc_done, axi_resp_done;
  logic [31:0]      axi_addr;
  logic [32:0]      axi_wdata;
  logic             axi_we, axi_we_q;
  logic [3:0]       axi_be;

  // Masters side outputs
  assign mstr_gnt_o    = (axi_fsm_q == AXI_ACC) & axi_acc_done;
  assign mstr_rdata_o  = RDATA_i;
  assign mstr_rvalid_o = (axi_fsm_q == AXI_RESP) & axi_resp_done;
  assign mstr_err_o    = (axi_fsm_q == AXI_RESP) & ((axi_we_q & BRESP_i[1]) | (~axi_we_q & RRESP_i[1]));

  // AXI side outputs
  assign AWID_o     = AXI_ID;
  assign AWADDR_o   = axi_addr;
  assign AWLEN_o    = 8'h0;
  assign AWSIZE_o   = 2'h2;
  assign AWBURST_o  = 2'h1;
  assign AWLOCK_o   = 1'b0;
  assign AWPROT_o   = 3'h1;
  assign AWCACHE_o  = 4'h0;
  assign AWUSER_o   = {USER_BIT_WIDTH{1'b0}};
  assign AWVALID_o  = (axi_fsm_q == AXI_ACC) & axi_we & ~aw_done;
  
  assign WDATA_o    = axi_wdata;
  assign WSTRB_o    = axi_be;
  assign WLAST_o    = 1'b1;
  assign WVALID_o   = (axi_fsm_q == AXI_ACC) & axi_we & ~w_done;

  assign BREADY_o   = 1'b1;
  
  assign ARID_o     = AXI_ID;
  assign ARADDR_o   = axi_addr;
  assign ARLEN_o    = 8'h0;
  assign ARSIZE_o   = 2'h2;
  assign ARBURST_o  = 2'h1;
  assign ARLOCK_o   = 1'b0;
  assign ARPROT_o   = 3'h1;
  assign ARCACHE_o  = 4'h0;
  assign ARUSER_o   = {USER_BIT_WIDTH{1'b0}};
  assign ARVALID_o  = (axi_fsm_q == AXI_ACC) & ~axi_we;
  
  assign RREADY_o   = 1'b1;

  assign axi_wr_done   = (AWREADY_i | aw_done) & (WREADY_i | w_done); 
  assign axi_acc_done  = (~axi_we & ARREADY_i) | (axi_we & axi_wr_done);
  assign axi_resp_done = (axi_we_q & BVALID_i) | (~axi_we_q & RVALID_i);

  // gnt by strict priority assignment - mst_req[0] == highest priority
  for (genvar i = 0; i < nMSTR; i++) begin
    logic [7:0] pri_mask;
    assign pri_mask = 8'hff >> (8-i);      // max 8 masters, should be enough 
    assign mstr_gnt[i] = mstr_req_i[i] & ~(|(mstr_req_i & pri_mask));
  end

  // mux for mem side controls
  
  always_comb begin
    int i;

    axi_addr  = 32'h0;
    axi_wdata = 33'h0;
    axi_we    = 1'b0;
    axi_be    = 4'h0;

    for (i = 0; i < nMSTR; i++) begin
      axi_addr  = axi_addr  | (mstr_addr_i[i] & {32{mstr_gnt_q[i]}});
      axi_wdata = axi_wdata | (mstr_wdata_i[i] & {33{mstr_gnt_q[i]}});
      axi_we    = axi_we    | (mstr_we_i[i] & mstr_gnt_q[i]);
      axi_be    = axi_be    | (mstr_be_i[i] & {4{mstr_gnt_q[i]}});
    end 

  end

  always @(posedge clk_i or negedge rstn_i) begin
    if(~rstn_i) begin
      mstr_gnt_q <= 0;
      axi_we_q   <= 1'b0;
      aw_done    <= 1'b0;
      w_done     <= 1'b0;
      axi_fsm_q  <= AXI_IDLE;
    end else begin

      // let's do a simple sequential state machine since we don't really care about 
      // performance over AXI in FPGA
      case (axi_fsm_q)
        AXI_IDLE:
          if (mstr_req_i != 0) begin
            axi_fsm_q  <= AXI_ACC;
            mstr_gnt_q <= mstr_gnt;      // latch gnt decision
            w_done     <= 1'b0;
            aw_done    <= 1'b0;
          end
        AXI_ACC:
          begin 
            if (AWREADY_i) aw_done <= 1'b1;
            if (WREADY_i)  w_done  <= 1'b1;

            if ((~axi_we & ARREADY_i) | (axi_we & axi_wr_done)) begin
              axi_fsm_q <= AXI_RESP;
              axi_we_q  <= axi_we;         // latch transaction type 
            end
          end
        AXI_RESP:
          if (axi_resp_done) axi_fsm_q <= AXI_IDLE;
        default:
          axi_fsm_q <= AXI_IDLE;
      endcase
    end
  end

endmodule


module ibexc_obimux3w0 #(
    parameter AXI_ID               = 4'h0,
    parameter USER_BIT_WIDTH       = 12
   ) (
  input                 clk_i,
  input                 rstn_i,

  input                 data_req_i,
  output                data_gnt_o,
  input [31:0]          data_addr_i,
  input [3:0]           data_be_i,
  input [32:0]          data_wdata_i, 
  input                 data_we_i, 

  output [32:0]         data_rdata_o,
  output                data_rvalid_o,
  output                data_error_o,
  
  input                 instr_req_i,
  output                instr_gnt_o,
  input [31:0]          instr_addr_i,

  output [32:0]         instr_rdata_o,
  output                instr_rvalid_o,
  output                instr_error_o,

  input                 dbg_req_i,
  output                dbg_gnt_o,
  input [31:0]          dbg_addr_i,
  input [3:0]           dbg_be_i,
  input [32:0]          dbg_wdata_i,
  input                 dbg_we_i,

  output [32:0]         dbg_rdata_o,
  output                dbg_rvalid_o,
  output                dbg_error_o,

  output                DBGMEM_EN_o,
  output [31:0]         DBGMEM_ADDR_o,
  output [32:0]         DBGMEM_WDATA_o,
  output                DBGMEM_WE_o,
  output [3:0]          DBGMEM_BE_o,
  input  [32:0]         DBGMEM_RDATA_i,
  input                 DBGMEM_READY_i,
  input                 DBGMEM_ERROR_i,

  output                IROM_EN_o,
  output [31:0]         IROM_ADDR_o,
  output [32:0]         IROM_WDATA_o,
  output                IROM_WE_o,
  output [3:0]          IROM_BE_o,
  input  [32:0]         IROM_RDATA_i,
  input                 IROM_READY_i,
  input                 IROM_ERROR_i,

  output                IRAM_EN_o,
  output [31:0]         IRAM_ADDR_o,
  output [32:0]         IRAM_WDATA_o,
  output                IRAM_WE_o,
  output [3:0]          IRAM_BE_o,
  input  [32:0]         IRAM_RDATA_i,
  input                 IRAM_READY_i,
  input                 IRAM_ERROR_i,

  output                DRAM_EN_o,
  output [31:0]         DRAM_ADDR_o,
  output [32:0]         DRAM_WDATA_o,
  output                DRAM_WE_o,
  output [3:0]          DRAM_BE_o,
  input  [32:0]         DRAM_RDATA_i,
  input                 DRAM_READY_i,
  input                 DRAM_ERROR_i,

  output [3:0]          AWID_o,
  output [31:0]         AWADDR_o,
  output [7:0]          AWLEN_o,
  output [2:0]          AWSIZE_o,
  output [1:0]          AWBURST_o,
  output [1:0]          AWLOCK_o,
  output [2:0]          AWPROT_o,
  output [3:0]          AWCACHE_o,
  output [USER_BIT_WIDTH-1:0]         AWUSER_o,
  output                AWVALID_o,
  input                 AWREADY_i,

  output [31:0]         WDATA_o,
  output [3:0]          WSTRB_o,
  output                WLAST_o,
  output                WVALID_o,
  input                 WREADY_i,

  input  [3:0]          BID_i,
  input  [1:0]          BRESP_i,
  input                 BVALID_i,
  output                BREADY_o,

  output [3:0]          ARID_o,
  output [31:0]         ARADDR_o,
  output [7:0]          ARLEN_o,
  output [2:0]          ARSIZE_o,
  output [1:0]          ARBURST_o,
  output [1:0]          ARLOCK_o,
  output [2:0]          ARPROT_o,
  output [3:0]          ARCACHE_o,
  output [USER_BIT_WIDTH-1:0]         ARUSER_o,
  output                ARVALID_o,
  input                 ARREADY_i,
  
  input  [3:0]          RID_i,
  input  [31:0]         RDATA_i,
  input                 RLAST_i,
  input  [1:0]          RRESP_i,
  input                 RVALID_i,
  output                RREADY_o,

  // DMA Controller Interface
  input                 dma_controller_req_i,
  output                dma_controller_gnt_o,
  input [31:0]          dma_controller_addr_i,
  input [3:0]           dma_controller_be_i,
  input [32:0]          dma_controller_wdata_i,
  input                 dma_controller_we_i,
  output [32:0]         dma_controller_rdata_o,
  output                dma_controller_rvalid_o,
  output                dma_controller_error_o,

  output                dma_conf_en_o,
  output [31:0]         dma_conf_addr_o,
  output [32:0]         dma_conf_wdata_o,
  output                dma_conf_we_o,
  output [3:0]          dma_conf_be_o,
  input  [32:0]         dma_conf_rdata_i,
  input                 dma_conf_ready_i,
  input                 dma_conf_error_i

);

  localparam nSLV = 6;
  localparam nMSTR = 4;

  logic [nSLV-1:0]       cpud_req;
  logic [31:0]           cpud_addr;
  logic [3:0]            cpud_be;
  logic [32:0]           cpud_wdata; 
  logic                  cpud_we; 
  logic [nSLV-1:0]       cpud_gnt;

  logic [nSLV-1:0]       cpui_req;
  logic [31:0]           cpui_addr;
  logic [3:0]            cpui_be;
  logic [32:0]           cpui_wdata; 
  logic                  cpui_we; 
  logic [nSLV-1:0]       cpui_gnt;

  logic [nSLV-1:0]       dbgm_req;
  logic [31:0]           dbgm_addr;
  logic [3:0]            dbgm_be;
  logic [32:0]           dbgm_wdata; 
  logic                  dbgm_we; 
  logic [nSLV-1:0]       dbgm_gnt;

  logic [nSLV-1:0][32:0] s2m_rdata; 
  logic [nSLV-1:0]       s2m_rvalid;
  logic [nSLV-1:0]       s2m_err;

  logic [nMSTR-1:0]      dbgmem_req;
  logic [nMSTR-1:0]      dbgmem_gnt;
  logic [32:0]           dbgmem_rdata; 
  logic                  dbgmem_rvalid;
  logic                  dbgmem_err;

  logic [nMSTR-1:0]      irom_req;
  logic [nMSTR-1:0]      irom_gnt;
  logic [32:0]           irom_rdata; 
  logic                  irom_rvalid;
  logic                  irom_err;

  logic [nMSTR-1:0]      iram_req;
  logic [nMSTR-1:0]      iram_gnt;
  logic [32:0]           iram_rdata; 
  logic                  iram_rvalid;
  logic                  iram_err;

  logic [nMSTR-1:0]      dram_req;
  logic [nMSTR-1:0]      dram_gnt;
  logic [32:0]           dram_rdata; 
  logic                  dram_rvalid;
  logic                  dram_err;
  
  logic [nMSTR-1:0]      axi_req;
  logic [nMSTR-1:0]      axi_gnt;
  logic [32:0]           axi_rdata; 
  logic                  axi_rvalid;
  logic                  axi_err;

  logic [nMSTR-1:0]      dma_conf_req;
  logic [nMSTR-1:0]      dma_conf_gnt;
  logic [32:0]           dma_conf_rdata; 
  logic                  dma_conf_rvalid;
  logic                  dma_conf_err;

  logic [nSLV-1:0]       dma_stream_req;
  logic [31:0]           dma_stream_addr;
  logic [3:0]            dma_stream_be;
  logic [32:0]           dma_stream_wdata;
  logic                  dma_stream_we;
  logic [nSLV-1:0]       dma_stream_gnt;

  logic [nMSTR-1:0][31:0]   m2s_addr;
  logic [nMSTR-1:0][3:0]    m2s_be;
  logic [nMSTR-1:0][32:0]   m2s_wdata; 
  logic [nMSTR-1:0]         m2s_we; 

  assign cpud_gnt = {dma_conf_gnt[0], axi_gnt[0], dram_gnt[0], iram_gnt[0], irom_gnt[0], dbgmem_gnt[0]};
  assign cpui_gnt = {dma_conf_gnt[1], axi_gnt[1], dram_gnt[1], iram_gnt[1], irom_gnt[1], dbgmem_gnt[1]};
  assign dbgm_gnt = {dma_conf_gnt[2], axi_gnt[2], dram_gnt[2], iram_gnt[2], irom_gnt[2], dbgmem_gnt[2]};
  
  assign dma_stream_gnt = {dma_conf_gnt[3], axi_gnt[3], dram_gnt[3], iram_gnt[3], irom_gnt[3], dbgmem_gnt[3]};

  assign s2m_rdata  = {dma_conf_rdata, axi_rdata, dram_rdata, iram_rdata, irom_rdata, dbgmem_rdata};   // shared
  assign s2m_rvalid = {dma_conf_rvalid, axi_rvalid, dram_rvalid, iram_rvalid, irom_rvalid, dbgmem_rvalid} ; // shared
  assign s2m_err    = {dma_conf_err, axi_err, dram_err, iram_err, irom_err, dbgmem_err} ; // shared

  assign dbgmem_req = {dma_stream_req[0], dbgm_req[0], cpui_req[0], cpud_req[0]};
  assign irom_req   = {dma_stream_req[1], dbgm_req[1], cpui_req[1], cpud_req[1]};
  assign iram_req   = {dma_stream_req[2], dbgm_req[2], cpui_req[2], cpud_req[2]};
  assign dram_req   = {dma_stream_req[3], dbgm_req[3], cpui_req[3], cpud_req[3]};
  assign axi_req    = {dma_stream_req[4], dbgm_req[4], cpui_req[4], cpud_req[4]};
  assign dma_conf_req = {dma_stream_req[5], dbgm_req[5], cpui_req[5], cpud_req[5]};

  assign m2s_addr   = {dma_stream_addr, dbgm_addr, cpui_addr, cpud_addr};      // shared
  assign m2s_be     = {dma_stream_be, dbgm_be, cpui_be, cpud_be};            // shared
  assign m2s_we     = {dma_stream_we, dbgm_we, cpui_we, cpud_we};            // shared
  assign m2s_wdata  = {dma_stream_wdata, dbgm_wdata, cpui_wdata, cpud_wdata};   // shared

  //
  // Master-side muxes
  //
  mstr_mux u_cpud_mstr_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (data_req_i),
    .mstr_gnt_o      (data_gnt_o),
    .mstr_addr_i     (data_addr_i),
    .mstr_be_i       (data_be_i),
    .mstr_wdata_i    (data_wdata_i),
    .mstr_we_i       (data_we_i), 
    .mstr_rdata_o    (data_rdata_o),
    .mstr_rvalid_o   (data_rvalid_o),
    .mstr_err_o      (data_error_o),
    .slv_req_o       (cpud_req),
    .slv_addr_o      (cpud_addr),
    .slv_be_o        (cpud_be),
    .slv_wdata_o     (cpud_wdata),
    .slv_we_o        (cpud_we), 
    .slv_gnt_i       (cpud_gnt),
    .slv_rdata_i     (s2m_rdata),
    .slv_rvalid_i    (s2m_rvalid),
    .slv_err_i       (s2m_err)
  );

  mstr_mux u_cpui_mstr_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (instr_req_i),
    .mstr_gnt_o      (instr_gnt_o),
    .mstr_addr_i     (instr_addr_i),
    .mstr_be_i       (4'b1111),
    .mstr_wdata_i    (33'h0),
    .mstr_we_i       (1'b0), 
    .mstr_rdata_o    (instr_rdata_o),
    .mstr_rvalid_o   (instr_rvalid_o),
    .mstr_err_o      (instr_error_o),
    .slv_req_o       (cpui_req),
    .slv_addr_o      (cpui_addr),
    .slv_be_o        (cpui_be),
    .slv_wdata_o     (cpui_wdata),
    .slv_we_o        (cpui_we), 
    .slv_gnt_i       (cpui_gnt),
    .slv_rdata_i     (s2m_rdata),
    .slv_rvalid_i    (s2m_rvalid),
    .slv_err_i       (s2m_err)
  );

  mstr_mux u_dbgm_mstr_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (dbg_req_i),
    .mstr_gnt_o      (dbg_gnt_o),
    .mstr_addr_i     (dbg_addr_i),
    .mstr_be_i       (dbg_be_i),
    .mstr_wdata_i    (dbg_wdata_i),
    .mstr_we_i       (dbg_we_i), 
    .mstr_rdata_o    (dbg_rdata_o),
    .mstr_rvalid_o   (dbg_rvalid_o),
    .mstr_err_o      (dbg_error_o),
    .slv_req_o       (dbgm_req),
    .slv_addr_o      (dbgm_addr),
    .slv_be_o        (dbgm_be),
    .slv_wdata_o     (dbgm_wdata),
    .slv_we_o        (dbgm_we), 
    .slv_gnt_i       (dbgm_gnt),
    .slv_rdata_i     (s2m_rdata),
    .slv_rvalid_i    (s2m_rvalid),
    .slv_err_i       (s2m_err)
  );

    // 
    // master interface comes from the dma controller
    // slave interface should be fed into memory and axi devices
    //
    mstr_mux u_dma_mstr_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (dma_controller_req_i),
    .mstr_gnt_o      (dma_controller_gnt_o),
    .mstr_addr_i     (dma_controller_addr_i),
    .mstr_be_i       (dma_controller_be_i),
    .mstr_wdata_i    (dma_controller_wdata_i),
    .mstr_we_i       (dma_controller_we_i), 
    .mstr_rdata_o    (dma_controller_rdata_o),
    .mstr_rvalid_o   (dma_controller_rvalid_o),
    .mstr_err_o      (dma_controller_error_o),
    .slv_req_o       (dma_stream_req),
    .slv_addr_o      (dma_stream_addr),
    .slv_be_o        (dma_stream_be),
    .slv_wdata_o     (dma_stream_wdata),
    .slv_we_o        (dma_stream_we), 
    .slv_gnt_i       (dma_stream_gnt),
    .slv_rdata_i     (s2m_rdata),
    .slv_rvalid_i    (s2m_rvalid),
    .slv_err_i       (s2m_err)
  );

  //
  // Slave-side muxes
  //
  slv_mem_mux u_dbg_mem_slv_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (dbgmem_req),
    .mstr_gnt_o      (dbgmem_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (dbgmem_rdata),
    .mstr_rvalid_o   (dbgmem_rvalid),
    .mstr_err_o      (dbgmem_err),
    .mem_en_o        (DBGMEM_EN_o),
    .mem_addr_o      (DBGMEM_ADDR_o),
    .mem_wdata_o     (DBGMEM_WDATA_o),
    .mem_we_o        (DBGMEM_WE_o),
    .mem_be_o        (DBGMEM_BE_o),
    .mem_rdata_i     (DBGMEM_RDATA_i),
    .mem_ready_i     (DBGMEM_READY_i),
    .mem_error_i     (DBGMEM_ERROR_i)
  );                 
    
  slv_mem_mux u_irom_slv_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (irom_req),
    .mstr_gnt_o      (irom_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (irom_rdata),
    .mstr_rvalid_o   (irom_rvalid),
    .mstr_err_o      (irom_err),
    .mem_en_o        (IROM_EN_o),
    .mem_addr_o      (IROM_ADDR_o),
    .mem_wdata_o     (IROM_WDATA_o),
    .mem_we_o        (IROM_WE_o),
    .mem_be_o        (IROM_BE_o),
    .mem_rdata_i     (IROM_RDATA_i),
    .mem_ready_i     (IROM_READY_i),
    .mem_error_i     (IROM_ERROR_i)
  );                 

  slv_mem_mux u_iram_slv_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (iram_req),
    .mstr_gnt_o      (iram_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (iram_rdata),
    .mstr_rvalid_o   (iram_rvalid),
    .mstr_err_o      (iram_err),
    .mem_en_o        (IRAM_EN_o),
    .mem_addr_o      (IRAM_ADDR_o),
    .mem_wdata_o     (IRAM_WDATA_o),
    .mem_we_o        (IRAM_WE_o),
    .mem_be_o        (IRAM_BE_o),
    .mem_rdata_i     (IRAM_RDATA_i),
    .mem_ready_i     (IRAM_READY_i),
    .mem_error_i     (IRAM_ERROR_i)
  );                 

  slv_mem_mux u_dram_slv_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (dram_req),
    .mstr_gnt_o      (dram_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (dram_rdata),
    .mstr_rvalid_o   (dram_rvalid),
    .mstr_err_o      (dram_err),
    .mem_en_o        (DRAM_EN_o),
    .mem_addr_o      (DRAM_ADDR_o),
    .mem_wdata_o     (DRAM_WDATA_o),
    .mem_we_o        (DRAM_WE_o),
    .mem_be_o        (DRAM_BE_o),
    .mem_rdata_i     (DRAM_RDATA_i),
    .mem_ready_i     (DRAM_READY_i),
    .mem_error_i     (IRAM_ERROR_i)
  );

    // 
    // master interface comes from the cpu
    // slave interface should be fed into cpu back as well
    //
    slv_mem_mux u_dma_slv_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (dma_conf_req),
    .mstr_gnt_o      (dma_conf_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (dma_conf_rdata),
    .mstr_rvalid_o   (dma_conf_rvalid),
    .mstr_err_o      (dma_conf_err),
    .mem_en_o        (dma_conf_en_o),
    .mem_addr_o      (dma_conf_addr_o),
    .mem_wdata_o     (dma_conf_wdata_o),
    .mem_we_o        (dma_conf_we_o),
    .mem_be_o        (dma_conf_be_o),
    .mem_rdata_i     (dma_conf_rdata_i),
    .mem_ready_i     (dma_conf_ready_i),
    .mem_error_i     (dma_conf_error_i)
  );

  slv_axi_mux u_slv_axi_mux (
    .clk_i           (clk_i), 
    .rstn_i          (rstn_i),
    .mstr_req_i      (axi_req),
    .mstr_gnt_o      (axi_gnt),
    .mstr_addr_i     (m2s_addr),
    .mstr_be_i       (m2s_be),
    .mstr_wdata_i    (m2s_wdata),
    .mstr_we_i       (m2s_we), 
    .mstr_rdata_o    (axi_rdata),
    .mstr_rvalid_o   (axi_rvalid),
    .mstr_err_o      (axi_err),
    .AWID_o          (AWID_o    ),    
    .AWADDR_o        (AWADDR_o  ),
    .AWLEN_o         (AWLEN_o   ),
    .AWSIZE_o        (AWSIZE_o  ),
    .AWBURST_o       (AWBURST_o ),
    .AWLOCK_o        (AWLOCK_o  ),
    .AWPROT_o        (AWPROT_o  ),
    .AWCACHE_o       (AWCACHE_o ),
    .AWUSER_o        (AWUSER_o  ),
    .AWVALID_o       (AWVALID_o ),
    .AWREADY_i       (AWREADY_i ),
    .WDATA_o         (WDATA_o   ),
    .WSTRB_o         (WSTRB_o   ),
    .WLAST_o         (WLAST_o   ),
    .WVALID_o        (WVALID_o  ),
    .WREADY_i        (WREADY_i  ),
    .BID_i           (BID_i     ),
    .BRESP_i         (BRESP_i   ),
    .BVALID_i        (BVALID_i  ),
    .BREADY_o        (BREADY_o  ),
    .ARID_o          (ARID_o    ),
    .ARADDR_o        (ARADDR_o  ),
    .ARLEN_o         (ARLEN_o   ),
    .ARSIZE_o        (ARSIZE_o  ),
    .ARBURST_o       (ARBURST_o  ),
    .ARLOCK_o        (ARLOCK_o   ),
    .ARPROT_o        (ARPROT_o   ),
    .ARCACHE_o       (ARCACHE_o  ),
    .ARUSER_o        (ARUSER_o   ),
    .ARVALID_o       (ARVALID_o  ),
    .ARREADY_i       (ARREADY_i  ),
    .RID_i           (RID_i      ),
    .RDATA_i         (RDATA_i    ),
    .RLAST_i         (RLAST_i    ),
    .RRESP_i         (RRESP_i    ),
    .RVALID_i        (RVALID_i   ),
    .RREADY_o        (RREADY_o   )   
    );

endmodule

