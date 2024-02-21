// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "dv_fcov_macros.svh"


//--------------------------------------------------------------------
//  Memory monitor core
//  End-to-end monitoring of data memory transactions
//--------------------------------------------------------------------
module mem_monitor import cheri_pkg::*; import cheriot_dv_pkg::*; # (
  parameter int unsigned srcID = 0
  ) (
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        src_lsu_req_valid,
  input  lsu_cmd_t    src_lsu_req,
  input  logic        src_lsu_resp_valid,
  input  lsu_cmd_t    src_lsu_resp,

  // monitor CPU data interface
  input  logic        data_req,
  input  logic        data_we,
  input  logic [3:0]  data_be,
  input  logic        data_is_cap,
  input  logic [31:0] data_addr,
  input  logic [32:0] data_wdata,

  input  logic        data_gnt,
  input  logic        data_rvalid,
  input  logic [32:0] data_rdata,
  input  logic        data_err,
  input  mem_cmd_t    data_resp_info,

  input  logic        end_sim_req
);

   //
   //  Function to convert from LSU commands to actual memory transaction (modeling LSU)
   //
   typedef struct {
     logic[1:0] valid;
     mem_cmd_t  cmd0; 
     mem_cmd_t  cmd1;
   } mem_2cmd_t;
  
  function automatic mem_2cmd_t lsu2mem_cmd (lsu_cmd_t lsu_cmd);
    mem_2cmd_t result;
    result.valid = 2'b00;

    if (lsu_cmd.is_cap) begin
      result.valid = 2'b11;

      result.cmd0.flag    = 8'h0;
      result.cmd0.is_cap  = 1'b1; 
      result.cmd0.we      = lsu_cmd.we;
      result.cmd0.be      = 4'hf;
      result.cmd0.addr32  = lsu_cmd.addr[31:2] - {31'h0, 1'b1}; // we capture at lsu_req_done (after addr_incr)
      result.cmd0.wdata   = {lsu_cmd.wcap.valid, lsu_cmd.wdata};
      result.cmd1.flag    = 8'h0;
      result.cmd1.is_cap  = 1'b1; 
      result.cmd1.we      = lsu_cmd.we;
      result.cmd1.be      = 4'hf;
      result.cmd1.addr32  = lsu_cmd.addr[31:2];
      result.cmd1.wdata   = reg2memcap_fmt0(lsu_cmd.wcap);  // QQQ add fmt1 support later

    end else if (lsu_cmd.rv32_type == 2'b00) begin          // full word
      logic [63:0] tmp64;
      logic  [7:0] tmp8;
      logic        unaligned;
  
      unaligned = (lsu_cmd.addr[1:0] != 0);
      result.valid = unaligned ? 2'b11 : 2'b01;
      tmp64 = {lsu_cmd.wdata, lsu_cmd.wdata} << {lsu_cmd.addr[1:0], 3'b000};
      tmp8  = 8'h0f << {lsu_cmd.addr[1:0]};

      result.cmd0.flag    = 8'h0;
      result.cmd0.is_cap  = 1'b0; 
      result.cmd0.we      = lsu_cmd.we;
      result.cmd0.be      = tmp8[3:0];
      result.cmd0.addr32  = lsu_cmd.addr[31:2] - {31'h0, unaligned}; // we capture at lsu_req_done (after addr_incr)
      result.cmd0.wdata   = {1'b0, tmp64[63:32]};

      result.cmd1.flag    = 8'h0;
      result.cmd1.is_cap  = 1'b0; 
      result.cmd1.we      = lsu_cmd.we;
      result.cmd1.be      = tmp8[7:4];
      result.cmd1.addr32  = lsu_cmd.addr[31:2];
      result.cmd1.wdata   = {1'b0, tmp64[63:32]};
    end else if (lsu_cmd.rv32_type == 2'b01) begin           // half word (CPU rv32 only)
      logic  [7:0] tmp8;
      logic        unaligned;

      // halfword accesses, ignore wdata here (will be checked by sail)
      unaligned = (lsu_cmd.addr[1:0] == 2'b11);
      result.valid = unaligned ? 2'b11 : 2'b01;
      tmp8 = 8'h03 << {lsu_cmd.addr[1:0]};

      result.cmd0.flag    = 8'h0;
      result.cmd0.is_cap  = 1'b0; 
      result.cmd0.we      = lsu_cmd.we;
      result.cmd0.be      = tmp8[3:0];
      result.cmd0.addr32  = lsu_cmd.addr[31:2] - {31'h0, unaligned};
      result.cmd0.wdata   = 33'hdead_beef;

      result.cmd1.flag    = 8'h0;
      result.cmd1.is_cap  = 1'b0; 
      result.cmd1.we      = lsu_cmd.we;
      result.cmd1.be      = tmp8[7:4];
      result.cmd1.addr32  = lsu_cmd.addr[31:2];
      result.cmd1.wdata   = 33'hdead_beef;
    end else begin                  // byte (CPU rv32 only)
      logic  [7:0] tmp8;

      result.valid = 2'b01;
      tmp8 = 8'h01 << {lsu_cmd.addr[1:0]};
      
      result.cmd0.flag    = 8'h0;
      result.cmd0.is_cap  = 1'b0; 
      result.cmd0.we      = lsu_cmd.we;
      result.cmd0.be      = tmp8[3:0];
      result.cmd0.addr32  = lsu_cmd.addr[31:2];
      result.cmd0.wdata   = {1'b0, lsu_cmd.wdata << {lsu_cmd.addr[1:0], 3'b000}};
    end

    return result;
  endfunction

  // check function: return 0 for pass, non-zero for fail
  function automatic logic[7:0] check_mem_cmd (mem_cmd_t cmd0, mem_cmd_t cmd1);
    logic [7:0] result;
   
    result = 0;

    if ((cmd0.is_cap != cmd1.is_cap) || (cmd0.we != cmd1.we) || (cmd0.be != cmd1.be))
      result |= 8'h1;
    if (cmd0.addr32 != cmd1.addr32) 
      result |= (8'h1 << 1);

    // QQQ skip wdata check here for now (unaligned/halfword/byte, etc)
    //if  (cmd0.we && (cmd0.wdata != cmd1.wdata))
    //  result |= (8'h1 << 2);

    return result;
  endfunction

  // check function: return 0 for pass, non-zero for fail
  // return a 8-bit value to help debugging causes
  function automatic logic[7:0] check_src_req_cap (lsu_cmd_t req, lsu_cmd_t resp, 
                                                    mem_cmd_t mem_resp0, mem_cmd_t mem_resp1);
    logic [7:0] result;
    reg_cap_t mcap;
   
    result = 0;

    if (resp.err != (mem_resp0.err || mem_resp1.err))
      result |= 8'h1;
    if ((~mem_resp0.is_cap) || (mem_resp0.we != req.we) || (mem_resp0.be != 4'hf) ||
        (mem_resp0.addr32[0]) || (mem_resp0.addr32 != (req.addr[31:2] - 1)))
      result |= (8'h1 << 1);
    if ((~mem_resp1.is_cap) || (mem_resp1.we != req.we) || (mem_resp1.be != 4'hf) ||
        (~mem_resp1.addr32[0]) || (mem_resp1.addr32 != (mem_resp0.addr32+1)))
      result |= (8'h1 << 2);

    // QQQ let's just do fmt0 for now and add fmt1 later
    if (req.we && ((mem_resp0.wdata[31:0] != req.wdata) || mem_resp1.wdata != reg2memcap_fmt0(req.wcap)))
      result |= (8'h1 << 3);
    if (~req.we && (mem_resp0.rdata[31:0] != resp.rdata))
      result |= (8'h1 << 4);
    
    mcap = mem2regcap_fmt0(mem_resp1.rdata, mem_resp0.rdata, 0);
    if (~req.we && (srcID == 0) && (~resp.err) &&       // ignore read cap for TBRE and STKZ
                    ((mcap.valid != resp.rcap.valid) || (mcap.top_cor != resp.rcap.top_cor) ||
                     (mcap.base_cor != resp.rcap.base_cor) || (mcap.exp != resp.rcap.exp) ||
                     (mcap.top != resp.rcap.top) || (mcap.base != resp.rcap.base) ||
                     (mcap.otype != resp.rcap.otype)))
      result |= (8'h1 << 5);

    // ignore perms for CPU reads now (clrperm not modeled yet). for TBRE/STKZ don't care
    // if (~req.we && (srcID != 0) && (mcap.cperms != resp.rcap.cperms))
    //  result |= (8'h1 << 6);

    return result;
  endfunction

  // check function: return 0 for pass, non-zero for fail
  function automatic logic [7:0] check_src_req_rv32_unaligned (lsu_cmd_t req, lsu_cmd_t resp, 
                                               mem_cmd_t mem_resp0, mem_cmd_t mem_resp1);
    logic [7:0]  result;

    result = 0;

    if (resp.err != (mem_resp0.err || mem_resp1.err))
      result |= 8'h1;
    if ((mem_resp0.is_cap) || (mem_resp0.we != req.we) || (mem_resp0.addr32 != (req.addr[31:2] - 1)))
      result |= (8'h1 << 1);
    if ((mem_resp1.is_cap) || (mem_resp1.we != req.we) ||
        (mem_resp1.addr32 != (mem_resp0.addr32+1)))
      result |= (8'h1 << 2);

    // QQQ add unaligned wdata/rdata check
    
    return result;
  endfunction

  // check function: return 0 for pass, non-zero for fail
  function automatic logic [7:0] check_src_req_rv32 (lsu_cmd_t req, lsu_cmd_t resp, mem_cmd_t mem_resp);
    logic [7:0] result;

    result = 0;

    if (resp.err != mem_resp.err)
      result |= 8'h1;
    if ((mem_resp.is_cap) || (mem_resp.we != req.we) || (mem_resp.addr32 != req.addr[31:2]))
      result |= (8'h1 << 1);
    
    if (req.we && (req.rv32_type == 2'b00) && (mem_resp.wdata[31:0] != req.wdata))
      result |= (8'h1 << 2);
    if (~req.we && ~resp.err && (req.rv32_type == 2'b00) && (mem_resp.rdata[31:0] != resp.rdata))
      result |= (8'h1 << 3);
    // QQQ add byte/hw wdata/rdata check
    
    return result;
  endfunction


  lsu_cmd_t lsu_req_queue[$], lsu_resp_queue[$];
  mem_cmd_t mem_req_queue[$], mem_resp_queue[$], src_mem_resp_queue[$];

  logic  mem_resp_src_sel;
  assign mem_resp_src_sel = data_resp_info.flag[srcID+1];

  // debug signals just for waveform viewing 
  logic [31:0] dbg_mem_req_size, dbg_mem_resp_size, dbg_src_mem_resp_size;
  logic [31:0] dbg_lsu_req_size, dbg_lsu_resp_size;

  lsu_cmd_t dbg_lsu_req_head, dbg_lsu_resp_head;
  mem_cmd_t dbg_mem_req_head, dbg_mem_resp_head, dbg_src_mem_resp_head;

  int unsigned lsu_req_cnt, mem_req_cnt, lsu_resp_cnt, src_mem_resp_cnt;
  logic [7:0] check_result_mem, check_result_src;

  logic sim_end;
  string mon_str;

  //
  //  main process (enqueue/dequeue/check)
  //
  initial begin
    mem_2cmd_t tmp_2cmd;
    logic      is_rv32_unaligned;

    lsu_req_queue  = {};
    lsu_resp_queue = {};
    mem_req_queue  = {};
    mem_resp_queue = {};
    src_mem_resp_queue = {};

    lsu_req_cnt      = 0;
    mem_req_cnt      = 0;
    lsu_resp_cnt     = 0;
    src_mem_resp_cnt = 0;

    check_result_mem = 0;
    check_result_src = 0;

    @(posedge rst_ni);

    while (1) begin
      @(posedge clk_i);

       dbg_mem_req_size = mem_req_queue.size();
       dbg_mem_resp_size = mem_resp_queue.size();
       dbg_src_mem_resp_size = src_mem_resp_queue.size();
       dbg_lsu_req_size = lsu_req_queue.size();
       dbg_lsu_resp_size = lsu_resp_queue.size();

      //
      // generate requests and place in scoreboard at the source side
      //
      if (src_lsu_req_valid) begin
        lsu_req_queue = {lsu_req_queue, src_lsu_req};
        lsu_req_cnt += 1;

        tmp_2cmd = lsu2mem_cmd(src_lsu_req);
        if (tmp_2cmd.valid[0]) mem_req_queue = {mem_req_queue, tmp_2cmd.cmd0};
        if (tmp_2cmd.valid[1]) mem_req_queue = {mem_req_queue, tmp_2cmd.cmd1};

        mem_req_cnt += tmp_2cmd.valid[0];
        mem_req_cnt += tmp_2cmd.valid[1];
      end

      // place the memory resp in an intermediate queue for compare later
      if (data_rvalid && mem_resp_src_sel) begin
        mem_resp_queue = {mem_resp_queue, data_resp_info};
      end

      //
      // comparison at memory interface
      //
      if ((mem_req_queue.size() > 0) && (mem_resp_queue.size() > 0)) begin
        dbg_mem_req_head = mem_req_queue[0];
        dbg_mem_resp_head = mem_resp_queue[0];

        check_result_mem = check_mem_cmd(mem_req_queue[0], mem_resp_queue[0]);
        if (check_result_mem != 0) $error("TB> %s: check failed: mem_req vs mem_resp", mon_str);

        src_mem_resp_queue = {src_mem_resp_queue, mem_resp_queue[0]};
        src_mem_resp_cnt += 1;

        mem_req_queue  = mem_req_queue[1:$];
        mem_resp_queue = mem_resp_queue[1:$];
      end

      // place the LSU response in an intermediate queue for compare later
      if (src_lsu_resp_valid) begin
        lsu_resp_queue = {lsu_resp_queue, src_lsu_resp};
        lsu_resp_cnt += 1;
      end

      //
      // Final comparison at the source side
      //   lsu_req vs lsu_resp vs src_mem_resp_queue
      if ((lsu_req_queue.size() > 0) && (lsu_resp_queue.size() > 0)) begin
        dbg_lsu_req_head = lsu_req_queue[0];
        dbg_lsu_resp_head = lsu_resp_queue[0];
        dbg_src_mem_resp_head = src_mem_resp_queue[0];

        is_rv32_unaligned = ((lsu_req_queue[0].rv32_type == 2'b00) && 
                            (lsu_req_queue[0].addr[1:0] != 2'b00)) || 
                            ((lsu_req_queue[0].rv32_type == 2'b01) && 
                            (lsu_req_queue[0].addr[1:0] == 2'b11));
  
        if (lsu_req_queue[0].is_cap && (src_mem_resp_queue.size() >= 2)) begin
          check_result_src = check_src_req_cap(lsu_req_queue[0], lsu_resp_queue[0], 
                                           src_mem_resp_queue[0],  src_mem_resp_queue[1]);
          if (check_result_src != 0) $error("TB> %s: check failed: src req vs resp 1", mon_str);

          lsu_req_queue  = lsu_req_queue[1:$];
          lsu_resp_queue = lsu_resp_queue[1:$];
          src_mem_resp_queue = src_mem_resp_queue[2:$];
        end else if (~lsu_req_queue[0].is_cap && is_rv32_unaligned && 
                      (src_mem_resp_queue.size() >= 2)) begin
          check_result_src = check_src_req_rv32_unaligned(lsu_req_queue[0], lsu_resp_queue[0], 
                                           src_mem_resp_queue[0],  src_mem_resp_queue[1]);
          if (check_result_src != 0) $error("TB> %s: check failed: src req vs resp 2", mon_str);

          lsu_req_queue  = lsu_req_queue[1:$];
          lsu_resp_queue = lsu_resp_queue[1:$];
          src_mem_resp_queue = src_mem_resp_queue[2:$];
        end else if (src_mem_resp_queue.size() > 0) begin
          check_result_src = check_src_req_rv32(lsu_req_queue[0], lsu_resp_queue[0], src_mem_resp_queue[0]);
          if (check_result_src != 0) $error("TB> %s: check failed: src_req vs resp 3", mon_str);

          lsu_req_queue  = lsu_req_queue[1:$];
          lsu_resp_queue = lsu_resp_queue[1:$];
          src_mem_resp_queue = src_mem_resp_queue[1:$];
        end
      end
    end
  end

  //
  // print out stats at the end of simulation
  // 
  initial begin

    if (srcID == 0) $sformat(mon_str, "CPU mem mon");
    if (srcID == 1) $sformat(mon_str, "STKZ mem mon");
    if (srcID == 2) $sformat(mon_str, "TBRE mem mon");

    sim_end = 1'b0;
    @(posedge rst_ni);

    while (1) begin
      @(posedge clk_i);
      if (end_sim_req) begin
        $display("TB> %s: counters: lsu_req = %d, lsu_resp = %d, mem_req = %d, src_mem_resp = %d",
                  mon_str, lsu_req_cnt, lsu_resp_cnt,  mem_req_cnt, src_mem_resp_cnt);   
        $display("TB> %s: pending terms in queues: %d, %d, %d, %d, %d", mon_str,
                  dbg_mem_req_size, dbg_mem_resp_size, dbg_src_mem_resp_size, dbg_lsu_req_size,
                  dbg_lsu_resp_size);
        if ((lsu_req_cnt != lsu_resp_cnt) || (mem_req_cnt != src_mem_resp_cnt))
          $error("TB> %s: ERROR! memory transactions count mismatch", mon_str);
        if ((dbg_mem_req_size != 0) || (dbg_mem_resp_size != 0) || (dbg_src_mem_resp_size != 0) ||
            (dbg_lsu_req_size != 0) || (dbg_lsu_resp_size != 0))
          $error("TB> %s: ERROR! Unresolved transactions found", mon_str);
      end
    end

  end

endmodule


//--------------------------------------------------------------------
//  Memory monitor top-level
//
//--------------------------------------------------------------------
module mem_mon_top import cheri_pkg::*; import cheriot_dv_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_ni,

  // monitor CPU data interface
  input  logic        data_req,
  input  logic        data_we,
  input  logic [3:0]  data_be,
  input  logic        data_is_cap,
  input  logic [31:0] data_addr,
  input  logic [32:0] data_wdata,

  input  logic        data_gnt,
  input  logic        data_rvalid,
  input  logic [32:0] data_rdata,
  input  logic        data_err,
  input  mem_cmd_t    data_resp_info,

  output logic [7:0]  data_flag,
  input  logic        end_sim_req
);

  `define TBRE_PATH dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i
  `define STKZ_PATH dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i
  `define CPU_EX_PATH  dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex
  `define CPU_WB_PATH  dut.u_ibex_top.u_ibex_core.wb_stage_i
  `define CPU_LSU_PATH  dut.u_ibex_top.u_ibex_core.load_store_unit_i
  logic req_isr;
  logic req_cpu, req_tbre, req_stkz;

// Internal LSU interface checking 
//   -- counting and tracking transactions (initiator to LSU to memory) - need scoreboard fifos
//      -- track errors (memory faults)
//      -- track both reqs and responses
//   -- protocol checking on instruction interface

  //
  // Tracking CPU execution of startup/exception handler and
  // suppress error injection during the phase
  // 
  assign req_isr = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_executing &
                   dut.u_ibex_top.u_ibex_core.load_store_unit_i.lsu_req_i &
                   ~dut.u_ibex_top.u_ibex_core.load_store_unit_i.cur_req_is_tbre &
                   dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.controller_dv_ext_i.cpu_in_isr;

  assign req_cpu =  dut.u_ibex_top.u_ibex_core.load_store_unit_i.lsu_req_i &
                   ~dut.u_ibex_top.u_ibex_core.load_store_unit_i.cur_req_is_tbre;
  assign req_tbre = dut.u_ibex_top.u_ibex_core.load_store_unit_i.cur_req_is_tbre &
                    dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_lsu_req_o & 
                    dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.mstr_arbit_comb[1];
  assign req_stkz = dut.u_ibex_top.u_ibex_core.load_store_unit_i.cur_req_is_tbre &
                    dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_lsu_req_o & 
                    dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.mstr_arbit_comb[0];

  assign data_flag = {4'h0, req_tbre, req_stkz, req_cpu, req_isr};


  lsu_cmd_t cur_cpu_lsu_req, cur_cpu_lsu_resp;
  lsu_cmd_t cur_tbre_lsu_req, cur_tbre_lsu_resp;
  lsu_cmd_t cur_stkz_lsu_req, cur_stkz_lsu_resp;

  always_comb begin
    cur_tbre_lsu_req.is_cap    = `TBRE_PATH.tbre_lsu_is_cap_o;
    cur_tbre_lsu_req.we        = `TBRE_PATH.tbre_lsu_we_o;
    cur_tbre_lsu_req.rv32_type = 2'b00;
    cur_tbre_lsu_req.addr      = `TBRE_PATH.tbre_lsu_addr_o;
    cur_tbre_lsu_req.wdata     = `TBRE_PATH.tbre_lsu_wdata_o;
    cur_tbre_lsu_req.wcap      = NULL_REG_CAP;

    cur_tbre_lsu_resp.rdata    = `TBRE_PATH.lsu_tbre_raw_lsw_i[31:0];               
    cur_tbre_lsu_resp.rcap     = NULL_REG_CAP;       // don't compare for TBRE
    cur_tbre_lsu_resp.err      = `TBRE_PATH.lsu_tbre_resp_err_i;

    cur_stkz_lsu_req.is_cap    = `STKZ_PATH.stkz_lsu_is_cap_o;
    cur_stkz_lsu_req.we        = `STKZ_PATH.stkz_lsu_we_o;
    cur_stkz_lsu_req.rv32_type = 2'b00;
    cur_stkz_lsu_req.addr      = `STKZ_PATH.stkz_lsu_addr_o;
    cur_stkz_lsu_req.wdata     = `STKZ_PATH.stkz_lsu_wdata_o;
    cur_stkz_lsu_req.wcap      = NULL_REG_CAP;

    cur_stkz_lsu_resp.rdata    = 32'h0;
    cur_stkz_lsu_resp.rcap     = NULL_REG_CAP;  
    cur_stkz_lsu_resp.err      = `STKZ_PATH.lsu_stkz_resp_err_i;

    cur_cpu_lsu_req.is_cap     = `CPU_EX_PATH.lsu_is_cap_o;
    cur_cpu_lsu_req.we         = `CPU_EX_PATH.lsu_we_o;
    cur_cpu_lsu_req.rv32_type  = `CPU_EX_PATH.lsu_type_o;
    cur_cpu_lsu_req.addr       = `CPU_EX_PATH.lsu_addr_o;
    cur_cpu_lsu_req.wdata      = `CPU_EX_PATH.lsu_wdata_o;
    cur_cpu_lsu_req.wcap       = `CPU_EX_PATH.lsu_wcap_o;

    cur_cpu_lsu_resp.rdata     = `CPU_WB_PATH.rf_wdata_lsu_i;
    cur_cpu_lsu_resp.rcap      = `CPU_WB_PATH.rf_wcap_lsu_i;
    cur_cpu_lsu_resp.err       = `CPU_WB_PATH.lsu_resp_err_i;
    
  end
 
  logic cpu_lsu_req_valid, cpu_lsu_resp_valid;
  logic stkz_lsu_req_valid, stkz_lsu_resp_valid;
  logic tbre_lsu_req_valid, tbre_lsu_resp_valid;

  assign cpu_lsu_req_valid  = `CPU_EX_PATH.lsu_req_done_i & (~`CPU_EX_PATH.lsu_cheri_err_o);
  assign cpu_lsu_resp_valid = `CPU_WB_PATH.lsu_resp_valid_i & (~`CPU_LSU_PATH.lsu_err_is_cheri_o);

  assign stkz_lsu_req_valid  = `STKZ_PATH.lsu_stkz_req_done_i;
  assign stkz_lsu_resp_valid = `STKZ_PATH.lsu_stkz_resp_valid_i;

  assign tbre_lsu_req_valid  = `TBRE_PATH.lsu_tbre_req_done_i;
  assign tbre_lsu_resp_valid = `TBRE_PATH.lsu_tbre_resp_valid_i;


  logic [2:0] sim_end_q;
  logic       end_sim_req_q;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      sim_end_q     <= 3'h0;
      end_sim_req_q <= 1'b0;
    end else begin
      sim_end_q     <= {sim_end_q[1:0], (end_sim_req & ~end_sim_req_q)};
      end_sim_req_q <= end_sim_req;
    end  
  end

  mem_monitor # (
    .srcID (0)
  ) u_cpu_mem_monitor (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .src_lsu_req_valid   (cpu_lsu_req_valid),
    .src_lsu_req         (cur_cpu_lsu_req),
    .src_lsu_resp_valid  (cpu_lsu_resp_valid),
    .src_lsu_resp        (cur_cpu_lsu_resp),
    .data_req            (data_req),
    .data_we             (data_we),
    .data_be             (data_be),
    .data_is_cap         (data_is_cap),
    .data_addr           (data_addr),
    .data_wdata          (data_wdata),
    .data_gnt            (data_gnt),
    .data_rvalid         (data_rvalid),
    .data_rdata          (data_rdata),
    .data_err            (data_err),
    .data_resp_info      (data_resp_info),
    .end_sim_req         (sim_end_q[0])
  );
  

  mem_monitor # (
    .srcID (1)
  ) u_stkz_mem_monitor (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .src_lsu_req_valid   (stkz_lsu_req_valid),
    .src_lsu_req         (cur_stkz_lsu_req),
    .src_lsu_resp_valid  (stkz_lsu_resp_valid),
    .src_lsu_resp        (cur_stkz_lsu_resp),
    .data_req            (data_req),
    .data_we             (data_we),
    .data_be             (data_be),
    .data_is_cap         (data_is_cap),
    .data_addr           (data_addr),
    .data_wdata          (data_wdata),
    .data_gnt            (data_gnt),
    .data_rvalid         (data_rvalid),
    .data_rdata          (data_rdata),
    .data_err            (data_err),
    .data_resp_info      (data_resp_info),
    .end_sim_req         (sim_end_q[1])
  );

  mem_monitor # (
    .srcID (2)
  ) u_tbre_mem_monitor (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .src_lsu_req_valid   (tbre_lsu_req_valid),
    .src_lsu_req         (cur_tbre_lsu_req),
    .src_lsu_resp_valid  (tbre_lsu_resp_valid),
    .src_lsu_resp        (cur_tbre_lsu_resp),
    .data_req            (data_req),
    .data_we             (data_we),
    .data_be             (data_be),
    .data_is_cap         (data_is_cap),
    .data_addr           (data_addr),
    .data_wdata          (data_wdata),
    .data_gnt            (data_gnt),
    .data_rvalid         (data_rvalid),
    .data_rdata          (data_rdata),
    .data_err            (data_err),
    .data_resp_info      (data_resp_info),
    .end_sim_req         (sim_end_q[2])
  );

endmodule
