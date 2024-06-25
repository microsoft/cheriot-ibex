// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// data interface/memory model
//
module data_mem_model import cheriot_dv_pkg::*; ( 
  input  logic              clk,
  input  logic              rst_n,

  input  logic [2:0]        ERR_RATE,   
  input  logic [3:0]        GNT_WMAX,
  input  logic [3:0]        RESP_WMAX,

  input  logic              err_enable,
  input  logic              ignore_stkz,
 
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
  output mem_cmd_t          data_resp_info,

  input  logic              tsmap_cs,
  input  logic [15:0]       tsmap_addr,
  output logic [31:0]       tsmap_rdata,

  output logic [127:0]      mmreg_corein,
  input  logic [63:0]       mmreg_coreout,

  output logic [3:0]        err_enable_vec, 
  output logic [2:0]        intr_ack,
  output logic              uart_stop_sim
);
 
  localparam int unsigned DRAM_AW     = 16; 

  localparam int unsigned TSRAM_AW    = 10; 
  localparam int unsigned NMMRI       = 128/32;
  localparam int unsigned NMMRO       = 64/32;

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

  logic [31:0] tsram[0:2**TSRAM_AW-1];
  logic [TSRAM_AW-1:0] tsram_p0_addr32;
  logic [31:0]         tsram_p0_rdata;
  logic                tsram_p0_sel, tsram_p0_cs;
  logic                tsram_p0_err_schd;
  logic [TSRAM_AW-1:0] tsram_p1_addr32;

  logic [NMMRO-1:0][31:0] mmreg_coreout_regs; 
  logic [NMMRI-1:0][31:0] mmreg_corein_regs; 
  logic [31:0]            mmreg_rdata;
  logic                   mmreg_sel, mmreg_cs;
  logic [7:0]             mmreg_addr32;

  logic                   uart_cs0, uart_cs1;
  logic [7:0]             uart_addr32;

  logic [7:0]             mem_flag;

  mem_obi_if #(
    .DW         (33)
  ) u_mem_obj_if (
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .GNT_WMAX     (GNT_WMAX),
    .RESP_WMAX    (RESP_WMAX),
    .data_req     (data_req),
    .data_we      (data_we),
    .data_be      (data_be),
    .data_is_cap  (data_is_cap),
    .data_addr    (data_addr),
    .data_wdata   (data_wdata),
    .data_flag    (data_flag),
    .data_gnt     (data_gnt),
    .data_rvalid  (data_rvalid),
    .data_rdata   (data_rdata),
    .data_err     (data_err),
    .data_resp_info (data_resp_info),
    .mem_cs       (mem_cs),
    .mem_we       (mem_we),
    .mem_be       (mem_be),
    .mem_flag     (mem_flag),
    .mem_addr32   (mem_addr32),
    .mem_wdata    (mem_wdata),
    .mem_rdata    (mem_rdata),
    .mem_err      (mem_err)
  );

  //
  // memory signals (sampled @posedge clk)
  //
  logic dram_sel_q, tsram_p0_sel_q, mmreg_sel_q;
  logic mem_req_isr, mem_req_stkz;

  assign mem_req_stkz = mem_flag[2];
  assign mem_req_isr  = mem_flag[0];
  assign mem_rdata = dram_sel_q ? dram_rdata : (tsram_p0_sel_q ? {1'b0, tsram_p0_rdata} : 
                                              (mmreg_sel_q ? {1'b0, mmreg_rdata} : 33'h0));
  // mem_err is in themem_cs
  assign mem_err   = ~mem_req_isr & dram_sel ? dram_err_schd : (tsram_p0_sel ? tsram_p0_err_schd : 1'b0);

  //
  // DRAM (data RAM)
  // starting at 0x8000_0000
  //
  // don't generate memory access if
  //   - responds with an error, or
  //   - accesses from stkz is supposed to be ignored.
  assign dram_addr32 = mem_addr32[DRAM_AW-1:0];
  assign dram_sel    = mem_cs & mem_addr32[29] & (mem_addr32[28:DRAM_AW+1] == 0);   
  assign dram_cs     = dram_sel & ~mem_err & (~mem_req_stkz | ~ignore_stkz);   

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      dram_sel_q      <= 1'b0;
      tsram_p0_sel_q  <= 1'b0;
      mmreg_sel_q     <= 1'b0;
    end else begin
      dram_sel_q      <= dram_sel;
      tsram_p0_sel_q  <= tsram_p0_sel;
      mmreg_sel_q     <= mmreg_sel;
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

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      dram_err_schd <= 1'b0;
    end else begin
      if (~err_enable)
        dram_err_schd <= 1'b0;
      else if (dram_sel)
        dram_err_schd <= (ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-ERR_RATE))==0);
    end
  end 
  //
  // TSRAM (dual port RAM)
  //
  // starting at 0x8300_0000 byte address 
  assign tsram_p0_addr32 = mem_addr32[TSRAM_AW-1:0];
  assign tsram_p0_sel    = mem_cs && (mem_addr32[29:22] == 8'h83) && 
                           (mem_addr32[21] == 0) && (mem_addr32[20:DRAM_AW+2] == 0);
  assign tsram_p0_cs     = tsram_p0_sel & ~mem_err;

  assign tsram_p1_addr32 = tsmap_addr[TSRAM_AW-1:0];

  always @(posedge clk, negedge rst_n) begin
    int i;
    if (~rst_n) begin
      for (i=0; i<2**TSRAM_AW; i++) tsram[i] = 32'h0; // initialize tsram to match sail
    end else begin
      if (tsram_p0_cs && mem_we) begin
        // p0 read/write
        if(mem_be[0])
          tsram[tsram_p0_addr32][7:0]  <= mem_wdata[7:0];
        if(mem_be[1])
          tsram[tsram_p0_addr32][15:8] <= mem_wdata[15:8];
        if(mem_be[2])
          tsram[tsram_p0_addr32][23:16] <= mem_wdata[23:16];
        if(mem_be[3])
          tsram[tsram_p0_addr32][31:24] <= mem_wdata[31:24];
      end else if (tsram_p0_cs)
        tsram_p0_rdata <= tsram[tsram_p0_addr32];  

        // p1 readonly
      if (tsmap_cs)
        tsmap_rdata <= tsram[tsram_p1_addr32];
      else 
        tsmap_rdata <= 32'h0;
    end
  end

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      tsram_p0_err_schd <= 1'b0;
    end else begin
      if (~err_enable)
        tsram_p0_err_schd <= 1'b0;
      else if (tsram_p0_sel)
        tsram_p0_err_schd <= (ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-ERR_RATE))==0);
    end
  end 
 

  //
  // MMREG (memory-mapped registers)
  //
  // 0x8380_0000: TBRE control
  // 0x8380_0080: scratch register 0,1
  // 0x8380_0100: TB error_enable, Intr_ack
  // 
  //
  logic [64:0] tbre_ctrl_vec;
  logic        tbre_stat, tbre_stat_q;
  logic [7:0]  tbre_flag;
  logic        tbre_done;
  logic [30:0] tbre_epoch;
  logic [7:0]  mmreg_addr32_q;
  logic        tbre_err, stkz_active, stkz_err;
  logic [31:0] scratch_reg0, scratch_reg1;

  // starting at 0x8380_0000 byte address 
  assign mmreg_addr32 = mem_addr32[7:0];
  assign mmreg_sel    = mem_cs && (mem_addr32[29:22] == 8'h83) && 
                        (mem_addr32[21] == 1) && (mem_addr32[20:8] == 0);
  assign mmreg_cs     = mmreg_sel;

  assign tbre_flag    = 8'h55;  // tbre/sktz present
  assign mmreg_corein = {63'h0, tbre_ctrl_vec};
  assign tbre_stat    = mmreg_coreout[0];
  assign tbre_done    = tbre_stat_q & ~tbre_stat;

  assign tbre_err     = mmreg_coreout[1];
  assign stkz_active  = mmreg_coreout[4];
  assign stkz_err     = mmreg_coreout[5];

  always_comb begin
    case (mmreg_addr32_q[7:0])
      0: mmreg_rdata = tbre_ctrl_vec[31:0];  
      1: mmreg_rdata = tbre_ctrl_vec[63:32];  
      2: mmreg_rdata = {tbre_flag, 23'h0, tbre_ctrl_vec[64]};  
      3: mmreg_rdata = {tbre_epoch, tbre_stat};
      4: mmreg_rdata = {31'h0, tbre_err};  
      5: mmreg_rdata = {30'h0, stkz_err, stkz_active};
      32: mmreg_rdata = scratch_reg0;  
      33: mmreg_rdata = scratch_reg1;  
      default: mmreg_rdata = 32'hdead_beef; 
    endcase
  end

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      tbre_ctrl_vec     <= 65'h0;
      tbre_epoch        <= 31'h0;
      tbre_stat_q       <= 1'b0;
      mmreg_addr32_q    <= 0;
      intr_ack          <= 3'h0;
      err_enable_vec    <= 4'h0;
      scratch_reg0      <= 32'h0; 
      scratch_reg1      <= 32'h0; 
    end
    else begin
      if (mmreg_cs && mem_we && (mmreg_addr32 == 0))
        tbre_ctrl_vec[31:0]   <= mem_wdata;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 1))
        tbre_ctrl_vec[63:32]   <= mem_wdata;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 2))
        tbre_ctrl_vec[64]   <= mem_wdata[0];
      else if (tbre_stat)
        tbre_ctrl_vec[64]   <= 1'b0;        // self clear tbre_go signal

      tbre_stat_q    <= tbre_stat;
      mmreg_addr32_q <= mmreg_addr32;

      if (tbre_done) tbre_epoch <= tbre_epoch + 1;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h20))  // 0x8380_0080
        scratch_reg0 <= mem_wdata[31:0];
      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h21))  // 0x8380_0084
        scratch_reg1 <= mem_wdata[31:0];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h40))  // 0x8380_0100
        err_enable_vec <= mem_wdata[3:0];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h41))  // 0x8380_0104
        intr_ack <= mem_wdata[2:0];
      else
        intr_ack <= 3'h0;
    end
  end 

  //
  // 0x8380_0200: UART (also aliased to 0x1000_0000)
  //
  assign uart_addr32  = mem_addr32[7:0];
  assign uart_cs0      = mem_cs && (mem_addr32[29:22] == 8'h83) && (mem_addr32[21:8] == 14'h2000);
  assign uart_cs1      = mem_cs && (mem_addr32[29:22] == 8'h10) && (mem_addr32[21:8] == 14'h0000);

  // UART printout
  initial begin
    uart_stop_sim = 1'b0;
    @(posedge rst_n);

    while (1) begin
      @(posedge clk);
      if ((uart_cs0 && mem_we && (uart_addr32 == 'h80)) || 
          (uart_cs1 && mem_we && (uart_addr32 == 'h00)))  
        if (mem_wdata[7]) 
          uart_stop_sim = 1'b1;
       else 
          $write("%c", mem_wdata[7:0]);
    end
  end

endmodule
