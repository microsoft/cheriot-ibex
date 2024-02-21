// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Random TBRE/STKZ traffic generator
//
module tbre_bg_gen (
  input  logic              clk,
  input  logic              rst_n,

  input  logic [3:0]        TBRE_INTVL,  // 0 - no TBRE traffic
  input  logic [3:0]        STKZ_INTVL,  // 0 - no STKZ traffic

  input  logic              tbre_bg_en,
  input  logic              stkz_bg_en,

  output logic [127:0]      mmreg_corein,
  input  logic [63:0]       mmreg_coreout,

  output logic              tbre_active,
  output logic              stkz_active
  );

  import cheri_pkg::*;
  import cheriot_dv_pkg::*;

  // Memory area that TBRE walk-through is limited to
  // size_in_bytes and addresss. must be 8-byte aligned
  localparam logic [31:0] TBREAddrMin = 32'h8002_0000; 
  localparam logic [31:0] TBREAddrMax = 32'h8003_fff8;
  localparam logic [31:0] TBRELenMin  = 32'h10;   
  localparam logic [31:0] TBRELenMax  = 32'h800;

  localparam logic [31:0] STKZAddrMin = 32'h8000_0000; 
  localparam logic [31:0] STKZAddrMax = 32'h8003_fff8;
  localparam logic [31:0] STKZLenMin  = 32'h0;   
  localparam logic [31:0] STKZLenMax  = 32'h400;

  // Heap area where caps point to
  localparam logic [31:0] TestHeapBase = 32'h8002_0000;
  localparam logic [31:0] TestHeapSize = 32'h1000;

  task gen_tbre_dataset(input [31:0] start_addr, input [31:0] end_addr);
  begin
    int i, base, len;
    logic [31:0] rand32;
    logic [32:0] tmp0, tmp1;
    @(posedge clk);

    // generate data in DRAM to be walked through
    base = (start_addr - DRAMStartAddr)/4;
    len = (end_addr - start_addr)/8 + 1;   // TBRE end addr is inclusive
    // $display("tbre dram_start = %8x, len = %8x", dram_start, len);
    for (i = 0; i <len; i++) begin
      // construct a capability 
      //  - note this is a zero-length capability since addr=base=top but here we don't care.
      rand32 = $urandom();
      tmp0 = TestHeapBase + (rand32 % (TestHeapSize/4))*4;     //address
      tmp0 = {rand32[31], tmp0[31:0]};   // set tag value
      // add a redundant tag value and signature in perms/otype field to help checking
      tmp1 = {rand32[31], rand32[31], 9'h15a, 4'h0, tmp0[8:0], tmp0[8:0]};       
      u_tb_top.u_data_mem.dram[base + 2*i] = tmp0;
      u_tb_top.u_data_mem.dram[base + 2*i+1] = tmp1;
      // if (i == 0) $display("tmp0 = %09x, tmp1 = %09x", tmp0, tmp1);
    end

    // generate random shadow bits in TSRAM 
    base = (TestHeapBase - DRAMStartAddr)/256;  // each 32-bit word in tsam covers 256 bytes memory
    len  = TestHeapSize/256;
    for (i = 0; i <len; i++) begin
      u_tb_top.u_data_mem.tsram[base+i] = $urandom();
    end
  end
  endtask
  

  task check_tbre_result(input [31:0] start_addr, input [31:0] end_addr);
  begin
    int i, base, len, tsmap_addr, tsmap_offset;
    logic [31:0] rand32;
    logic [32:0] dw0, dw1;
    @(posedge clk);

    // generate data in DRAM to be walked through
    base = (start_addr - DRAMStartAddr)/4;
    len = (end_addr - start_addr)/8 + 1;   // TBRE end addr is inclusive
    // $display("dram_start = %8x, len = %8x", base, len);
    for (i = 0; i <len; i++) begin
      dw0 = u_tb_top.u_data_mem.dram[base + 2*i];
      dw1 = u_tb_top.u_data_mem.dram[base + 2*i+1];
      if ((dw0 < TestHeapBase) && (dw0 >= TestHeapBase+TestHeapSize))
        $error("TB> tbre_bg_gen: check_result ptr ERROR %d", i);

      // clear tags on dw0 when shdw == 1, don't write when shdw == 0
      tsmap_addr = (dw0 - DRAMStartAddr) >> 8;
      tsmap_offset = dw0 - DRAMStartAddr;
      tsmap_offset = tsmap_offset[7:3];
      if ((u_tb_top.u_data_mem.tsram[tsmap_addr][tsmap_offset] && dw0[32]) ||
          (~u_tb_top.u_data_mem.tsram[tsmap_addr][tsmap_offset] && (dw0[32]!=dw1[32])))
        $error("TB> tbre_bg_gen: check_result tag ERROR, %x, %x/%x, %x, %x, %x", 
                i, dw0, dw1, tsmap_addr, tsmap_offset, u_tb_top.u_data_mem.tsram[tsmap_addr]);

      // check dw1 to make sure we didn't overwrite the wrong location       
      if ((dw1[32] != dw1[31]) || (dw1[30:22] != 9'h15a) || (dw1[21:18] != 0) ||
          (dw1[17:9] != dw1[8:0]) || (dw0[8:0] != dw1[8:0]))
        $error("TB> tbre_bg_gen: check_result dw1 ERROR, %x, %x", dw0, dw1);
    end
  end
  endtask

  //
  // Controlling TBRE via mmreg interface
  //
  logic        tbre_stat, tbre_stat_q;
  logic [31:0] tbre_start_addr, tbre_end_addr;
  logic        tbre_go;

  assign mmreg_corein = {63'h0, tbre_go, tbre_end_addr, tbre_start_addr}; 
  assign tbre_stat    = mmreg_coreout[0];

  initial begin: tbre_stimuli
    int nwait, i;
    logic [31:0] rand32, tmp32;

    tbre_start_addr = 32'h0;
    tbre_end_addr   = 32'h0;
    tbre_go         = 1'b0;
    tbre_active     = 1'b0;


    @(posedge rst_n);

    while (1) begin
      if (~tbre_bg_en || (TBRE_INTVL == 0)) begin
        tbre_active = 1'b0;
        @(posedge clk);
      end else begin
        tbre_active = 1'b1;
        @(posedge clk);

        rand32 = $urandom();
        nwait = ((rand32 % (2** TBRE_INTVL)) + 1) * 10;   // wait at least 10 clk cycles
        repeat (nwait) @(posedge clk);
        if (tbre_bg_en) begin
          // compute start/end address
          rand32 = $urandom();
          tmp32  = rand32 % ((TBREAddrMax - TBREAddrMin - TBRELenMin)/8);
          tbre_start_addr =  TBREAddrMin + {tmp32[28:0], 3'h0};
          rand32 = $urandom();
          tmp32 = (rand32 % (TBRELenMax - TBRELenMin)) + TBRELenMin;
          tbre_end_addr = tbre_start_addr + {tmp32[31:3], 3'h0};
          if (tbre_end_addr > TBREAddrMax) tbre_end_addr = TBREAddrMax;
          //$display("tbre start = %8x, end = %8x", tbre_start_addr, tbre_end_addr);
          gen_tbre_dataset(tbre_start_addr, tbre_end_addr);     // generate input data set for TBRE runs

          tbre_go     = 1'b1;
          @(posedge clk);
          @(posedge clk);
          tbre_go     = 1'b0;
          
          while (tbre_stat) @(posedge clk);     // wait TBRE hardware done
          check_tbre_result(tbre_start_addr, tbre_end_addr);
          @(posedge clk);
        end    // kick TBRE
      end    // if enable /else
    end   // while
  end

  //
  // Controlling STKZ via foring ZTOPC interface
  //   - when background generation enabled, data_mem_model will ignore the STKZ writes
  //     therefore we don't have to worry about stkz overwrites memory content and corrupt tests
  //
  
  `define STKZ_PATH dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i
  `define ID_PATH   dut.u_ibex_top.u_ibex_core.id_stage_i

  logic        stkz_stat;
  logic [31:0] stkz_start_addr, stkz_end_addr;
  full_cap_t   ztop_wfcap;
  logic [31:0] ztop_wdata;
  logic        cpu_instr_done;
  
  assign stkz_stat = `STKZ_PATH.stkz_active_o;
  assign cpu_instr_done  = `ID_PATH.instr_done;

  initial begin: stkz_stimuli    
    int nwait, i;
    logic [31:0] rand32, tmp32;

    stkz_start_addr = 32'h0;
    stkz_end_addr   = 32'h0;
    stkz_active     = 1'b0;


    @(posedge rst_n);

    while (1) begin
      if (~stkz_bg_en || (STKZ_INTVL == 0)) begin
        stkz_active = 1'b0;
        @(posedge clk);
      end else begin
        stkz_active = 1'b1;
        @(posedge clk);

        rand32 = $urandom();
        nwait = ((rand32 % (2** STKZ_INTVL)) + 1) * 10;   // wait at least 10 clk cycles
        repeat (nwait) @(posedge clk);
        if (stkz_bg_en) begin
          // compute start/end address
          rand32 = $urandom();
          tmp32  = rand32 % ((STKZAddrMax - STKZAddrMin - STKZLenMin)/16) + 1; // 1 to 0x4000 (in 16-B granule)
          stkz_start_addr =  STKZAddrMin + {tmp32[27:0], 4'h0};
          rand32 = $urandom();
          tmp32 = (rand32 % (STKZLenMax - STKZLenMin)) + STKZLenMin;
          stkz_end_addr = stkz_start_addr - {tmp32[31:4], 4'h0};
          if (stkz_end_addr < STKZAddrMin) stkz_end_addr = STKZAddrMin;

          //$display("stkz start = %8x, end = %8x", stkz_start_addr, stkz_end_addr);
          ztop_wfcap.valid = 1'b1;
          ztop_wfcap.top33 = stkz_start_addr;
          ztop_wfcap.base32 = stkz_end_addr;

          // don't issue bg ztop write in the middle of a CPU LSU transaction
          force `STKZ_PATH.ztop_wr_i = cpu_instr_done;
          force `STKZ_PATH.ztop_wfcap_i = ztop_wfcap;
          force `STKZ_PATH.ztop_wdata_i = stkz_start_addr;

          @(posedge clk);
          while (~cpu_instr_done) @(posedge clk);

          release `STKZ_PATH.ztop_wr_i;
          release `STKZ_PATH.ztop_wfcap_i;
          release `STKZ_PATH.ztop_wdata_i;
 
          @(posedge clk);
          while (stkz_stat) @(posedge clk);     // wait TBRE hardware done
          @(posedge clk);
        end  
      end    // if enable /else
    end   // while
  end

endmodule
