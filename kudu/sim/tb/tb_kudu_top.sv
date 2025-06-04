// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps
//`define BOOT_ADDR 32'h8000_0000
`define BOOT_ADDR 32'h8000_0000

module tb_kudu_top; 
`ifndef IBEX
  import super_pkg::*;
  localparam DBusW = MemW;
`else
  import ibex_pkg::*;
  import cheri_pkg::*;
  `ifdef CHERIoT
    localparam DBusW = 65;
  `else
    localparam DBusW = 32;
  `endif
`endif

  import kudu_dv_pkg::*;


  logic        cheri_pmode;
  logic        cheri_tsafe_en;

  logic        clk, rst_n;

  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [63:0] instr_rdata;
  logic        instr_err;

  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [DBusW-1:0] data_wdata;
  logic [DBusW-1:0] data_rdata;
  logic        data_err;
  logic        data_is_cap;
  logic [7:0]  data_flag;
  mem_cmd_t    data_resp_info;

  logic        irq_external;
  logic        irq_software;
  logic        irq_timer;

  logic        tsmap_cs;
  logic [15:0] tsmap_addr;
  logic [31:0] tsmap_rdata;

  logic        uart_stop_sim;
  logic        debug_req;

  logic        mcycle_rd_event;
  logic        stat_print_req;

  logic [2:0]  irq_vec, intr_ack;

  logic        intr_enable;
  logic        instr_err_enable, data_err_enable, cap_err_enable;
  logic        cfg_intr_enable;
  logic        cfg_instr_err_enable, cfg_data_err_enable, cfg_cap_err_enable;

  int unsigned cfg_instr_err_rate, cfg_data_err_rate;
  int unsigned cfg_instr_gnt_wmax, cfg_data_gnt_wmax;
  int unsigned cfg_instr_resp_wmax, cfg_data_resp_wmax;
  int unsigned cfg_intr_intvl;
  int unsigned cfg_dbg_req_intvl;
  int unsigned cfg_cap_err_rate;

  logic [2:0] instr_err_rate, data_err_rate;
  logic [3:0] instr_gnt_wmax, data_gnt_wmax;
  logic [3:0] instr_resp_wmax, data_resp_wmax;
  logic [3:0] intr_intvl;
 
  logic [2:0] cap_err_rate;
  logic [3:0] err_enable_vec;

  logic [3:0] dbg_req_intvl;

  task config_tb ();
    int i;
    instr_resp_wmax = 0;
    instr_gnt_wmax  = 0;
    instr_err_rate  = 0;

    data_resp_wmax = 0;
    data_gnt_wmax  = 0;
    data_err_rate  = 0;

    intr_intvl    = 0;
    cap_err_rate  = 0;
    dbg_req_intvl = 0;

    i = $value$plusargs("INSTR_ERR_RATE=%d", cfg_instr_err_rate);
    if (i == 1) instr_err_rate = cfg_instr_err_rate[2:0];
    i = $value$plusargs("INSTR_GNT_WMAX=%d", cfg_instr_gnt_wmax);
    if (i == 1) instr_gnt_wmax = cfg_instr_gnt_wmax[3:0];
    i = $value$plusargs("INSTR_RESP_WMAX=%d", cfg_instr_resp_wmax);
    if (i == 1) instr_resp_wmax = cfg_instr_resp_wmax[3:0];

    i = $value$plusargs("DATA_ERR_RATE=%d", cfg_data_err_rate);
    if (i == 1) data_err_rate = cfg_data_err_rate[2:0];
    i = $value$plusargs("DATA_GNT_WMAX=%d", cfg_data_gnt_wmax);
    if (i == 1) data_gnt_wmax = cfg_data_gnt_wmax[3:0];
    i = $value$plusargs("DATA_RESP_WMAX=%d", cfg_data_resp_wmax);
    if (i == 1) data_resp_wmax = cfg_data_resp_wmax[3:0];

    i = $value$plusargs("INTR_INTVL=%d", cfg_intr_intvl);
    if (i == 1) intr_intvl = cfg_intr_intvl[3:0];

    i = $value$plusargs("DBG_REQ_INTVL=%d", cfg_dbg_req_intvl);
    if (i == 1) dbg_req_intvl = cfg_dbg_req_intvl[3:0];

    i = $value$plusargs("CAP_ERR_RATE=%d", cfg_cap_err_rate);
    if (i == 1) cap_err_rate = cfg_cap_err_rate[2:0];

    $display("TB> MemDataWidth = %2d, CFG.cheri_pmode=%1d", 
             DBusW,  cheri_pmode);
    $display("TB> INSTR_GNTW = %d, INSTR_RESPW = %d, DATA_GNTW = %d, DATA_RESPW = %d", 
             instr_gnt_wmax, instr_resp_wmax, data_gnt_wmax, data_resp_wmax); 
    $display("TB> INSTR_ERR_RATE = %d, DATA_ERR_RATE = %d, INTR_INTVL = %d, CAP_ERR_RATE = %d", 
             instr_err_rate,  data_err_rate, intr_intvl, cap_err_rate);
    $display("TB> DBG_REQ_INTVL = %d", dbg_req_intvl);
  endtask

`ifdef CHERIoT
  assign cheri_pmode    = 1'b1;
  assign cheri_tsafe_en = 1'b1;
`else
  assign cheri_pmode    = 1'b0;
  assign cheri_tsafe_en = 1'b0;
`endif

  assign debug_req      = 1'b0;

  assign {irq_timer, irq_software,  irq_external} = irq_vec; 

`ifndef IBEX
  kudu_top #(
  `ifdef CHERIoT
    .CHERIoTEn   (1'b1),
  `else
    .CHERIoTEn   (1'b0),
  `endif
    .DualIssue   (1'b1),
    .EarlyLoad   (1'b1),
    .TwoStageIR  (1'b1),
    .DCacheEn    (1'b0),
    .HeapBase    (32'h8000_0000),
    .TSMapSize   (1024)
  ) dut (
    .clk_i                (clk         ),
    .rst_ni               (rst_n       ),
    .hart_id_i            ('0          ),
    .cheri_pmode_i        (cheri_pmode ),
    .boot_addr_i          (`BOOT_ADDR  ), // align with spike boot address
    .instr_req_o          (instr_req   ),
    .instr_gnt_i          (instr_gnt   ),
    .instr_rvalid_i       (instr_rvalid),
    .instr_addr_o         (instr_addr  ),
    .instr_rdata_i        (instr_rdata ),
    .instr_err_i          (instr_err   ),
    .data_req_o           (data_req    ),
    .data_gnt_i           (data_gnt    ),
    .data_rvalid_i        (data_rvalid ),
    .data_we_o            (data_we     ),
    .data_be_o            (data_be     ),
    .data_is_cap_o        (data_is_cap ),
    .data_addr_o          (data_addr   ),
    .data_wdata_o         (data_wdata  ),
    .data_rdata_i         (data_rdata  ),
    .data_err_i           (data_err    ),
    .tsmap_cs_o           (tsmap_cs    ),
    .tsmap_addr_o         (tsmap_addr  ),
    .tsmap_rdata_i        (tsmap_rdata ),
    .cheri_fatal_err_o    (),
    .irq_software_i       (irq_software),
    .irq_timer_i          (irq_timer   ),
    .irq_external_i       (irq_external),
    .irq_fast_i           (15'h0       )
  );

  logic ir0_mcycle_rd, ir1_mcycle_rd;
  assign ir0_mcycle_rd =  (dut.issuer_i.ir0_dec.insn[6:0] == 7'h73) && (dut.issuer_i.ir0_dec.insn[31:20] == 12'hB00);
  assign ir1_mcycle_rd =  (dut.issuer_i.ir1_dec.insn[6:0] == 7'h73) && (dut.issuer_i.ir1_dec.insn[31:20] == 12'hB00);

  assign mcycle_rd_event = ((|dut.issuer_i.ir0_pl_sel) & ir0_mcycle_rd) ||
                           ((|dut.issuer_i.ir1_pl_sel) & ir1_mcycle_rd) ;

  kudu_stats kudu_stats_i (
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .start_stop (mcycle_rd_event),
    .print_req  (stat_print_req)
  );


`endif

`ifdef IBEX
  logic [31:0] instr_rdata_ibex;

  ibex_top_tracing #(
                     .HeapBase        (32'h8000_0000),
                     .TSMapBase       (32'h8003_0000),
                     .TSMapSize       (1024),
                     .DmHaltAddr      (32'h8004_0000),
                     .DmExceptionAddr (32'h8004_0080),
                     .RV32M           (RV32MSingleCycle),
                     .MMRegDinW       (128),
                     .MMRegDoutW      (64),
                   `ifdef CHERIoT
                     .DataWidth       (65),
                   `else
                     .DataWidth       (32),
                   `endif
                     .CheriTBRE       (1'b0),
                     .CheriStkZ       (1'b0),
                     .CheriCapIT8     (1'b1)
  ) dut (
    .clk_i                (clk         ),
    .rst_ni               (rst_n       ),
    .test_en_i            (1'b0        ),
    .scan_rst_ni          (1'b1        ),
    .ram_cfg_i            ('{0, 0}     ),
    .hart_id_i            ('0          ),
    .cheri_pmode_i        (cheri_pmode ),
    .cheri_tsafe_en_i     (cheri_tsafe_en ),
    .boot_addr_i          (`BOOT_ADDR  ), // align with spike boot address
    .debug_req_i          (debug_req   ),
    .fetch_enable_i       (4'b1001     ),
    .instr_req_o          (instr_req   ),
    .instr_gnt_i          (instr_gnt   ),
    .instr_rvalid_i       (instr_rvalid),
    .instr_addr_o         (instr_addr  ),
    .instr_rdata_i        (instr_rdata_ibex),
    .instr_rdata_intg_i   (7'h0),
    .instr_err_i          (instr_err   ),
    .data_req_o           (data_req    ),
    .data_gnt_i           (data_gnt    ),
    .data_rvalid_i        (data_rvalid ),
    .data_we_o            (data_we     ),
    .data_be_o            (data_be     ),
    .data_is_cap_o        (data_is_cap ),
    .data_addr_o          (data_addr   ),
    .data_wdata_o         (data_wdata),
    .data_rdata_i         (data_rdata),
    .data_rdata_intg_i    (7'h0),
    .data_err_i           (data_err    ),
    .tsmap_cs_o           (tsmap_cs),
    .tsmap_addr_o         (tsmap_addr),
    .tsmap_rdata_i        (tsmap_rdata),
    .tsmap_rdata_intg_i   (7'h0),
    .mmreg_corein_i       (128'h0),
    .mmreg_coreout_o      (),
    .cheri_fatal_err_o    (),
    .irq_software_i       (irq_software),
    .irq_timer_i          (irq_timer   ),
    .irq_external_i       (irq_external),
    .irq_fast_i           (15'h0       ),
    .irq_nm_i             (1'b0        ), 
    .scramble_key_valid_i (1'b0        ),
    .scramble_key_i       (128'h0      ),
    .scramble_nonce_i     (64'h0       ),
    .core_sleep_o         (),
    .double_fault_seen_o  (),
    .crash_dump_o         (),
    .scramble_req_o       (),
    .data_wdata_intg_o    ()
  );

  logic addr_b2_q;
  assign instr_rdata_ibex = addr_b2_q ? instr_rdata[63:32] : instr_rdata[31:0];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      addr_b2_q <= 0;
    end else if (instr_gnt) begin
      addr_b2_q <= instr_addr[2];
    end
  end

  assign mcycle_rd_event = (dut.u_ibex_top.u_ibex_core.csr_op == 0) && 
                           (dut.u_ibex_top.u_ibex_core.csr_addr == 12'hB00);

  ibex_stats ibex_stats_i (
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .start_stop (mcycle_rd_event),
    .print_req  (stat_print_req)
  );

`endif

  initial begin
    #0 $fsdbDumpfile("tb_kudu_top.fsdb");
    $fsdbDumpvars(0, "+all", tb_kudu_top); 
  end


  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #5 clk = ~clk;
    end
  end

  //
  // simulation init
  //
  string test_name, vhx_path;

  initial begin
    bit cont_flag;
    int i, timeout, cycle_cnt;

    timeout = 20*1000*1000;   // default timeout
    timeout = 1000* 1000;   // default timeout

    i = $value$plusargs("TEST=%s", test_name);
    if (i == 0) $sformat(test_name, "hello_world");
    i = $value$plusargs("TIMEOUT=%d", timeout);

    $sformat(vhx_path, "./bin/%s.vhx", test_name);
    $display("TB> Loading test %s", test_name);
    $display("TB> Test timeout = %d", timeout);

    config_tb();
    {cfg_instr_err_enable, cfg_data_err_enable, cfg_intr_enable, cfg_cap_err_enable} = 4'h0;

    stat_print_req = 1'b0;
    cycle_cnt     = 0;
    rst_n = 1'b1;
    #1;
    rst_n = 1'b0;

    $readmemh(vhx_path, u_instr_mem.iram, 'h0);   // load main executable
    $readmemh(vhx_path, u_data_mem.dram, 'h0);   // load main executable


    repeat(10) @(posedge clk);
    rst_n = 1'b1;

    {cfg_instr_err_enable, cfg_data_err_enable, cfg_intr_enable, cfg_cap_err_enable} = 4'hf;
 
    cont_flag = 1;
    while (cont_flag) begin
      @(posedge clk);
      cycle_cnt ++;
      if (cycle_cnt > timeout) begin
        cont_flag = 0;
        $display("TB> Simulation timed out after %d cycles", cycle_cnt);
      end
     
      if (uart_stop_sim) begin
        cont_flag = 0;
        $display("TB> Simulation stopped by UART request @ %d cycles", cycle_cnt);
        {cfg_instr_err_enable, cfg_data_err_enable, cfg_intr_enable, cfg_cap_err_enable} = 4'h0;
        @(posedge clk);
        stat_print_req = 1'b1;
        @(posedge clk);
        stat_print_req = 1'b0;

      end
    end
    
    repeat (5) @(posedge clk);

    $finish();
  end

  assign instr_err_enable = cfg_instr_err_enable & err_enable_vec[0];
  assign data_err_enable  = cfg_data_err_enable & err_enable_vec[1];
  assign intr_enable      = cfg_intr_enable & err_enable_vec[2];
  assign cap_err_enable   = cfg_cap_err_enable & err_enable_vec[3];

  //
  // RAMs 
  //
  instr_mem_model # (
   `ifndef IBEX
    .UnalignedFetch(1'b1)
   `else
    .UnalignedFetch(1'b0)
   `endif
  ) u_instr_mem (
    .clk             (clk           ), 
    .rst_n           (rst_n         ),
    .ERR_RATE        (instr_err_rate),
    .GNT_WMAX        (instr_gnt_wmax),
    .RESP_WMAX       (instr_resp_wmax),
    .err_enable      (instr_err_enable),
    .instr_req       (instr_req     ),
    .instr_addr      (instr_addr    ),
    .instr_gnt       (instr_gnt     ),
    .instr_rvalid    (instr_rvalid  ),
    .instr_rdata     (instr_rdata),
    .instr_err       (instr_err     )
  );
  
  logic [64:0] data_rdata65, data_wdata65;

  assign data_flag = 8'h0;

  assign data_rdata   = data_rdata65[DBusW-1:0];
  assign data_wdata65 = data_wdata;

  data_mem_model #(.DW(65)) u_data_mem (
    .clk             (clk          ), 
    .rst_n           (rst_n        ),
    .ERR_RATE        (data_err_rate),
    .GNT_WMAX        (data_gnt_wmax),
    .RESP_WMAX       (data_resp_wmax),
    .err_enable      (data_err_enable),
    .data_req        (data_req     ),
    .data_we         (data_we      ),
    .data_be         (data_be      ),
    .data_is_cap     (data_is_cap  ),
    .data_addr       (data_addr    ),
    .data_wdata      (data_wdata65 ),
    .data_flag       (data_flag    ),   // from mem_monitor
    .data_gnt        (data_gnt     ),
    .data_rvalid     (data_rvalid  ),
    .data_rdata      (data_rdata65 ),
    .data_err        (data_err     ),
    .data_resp_info  (data_resp_info),  // to mem_monitor
    .tsmap_cs        (tsmap_cs     ),
    .tsmap_addr      (tsmap_addr   ),
    .tsmap_rdata     (tsmap_rdata  ),
    .err_enable_vec  (err_enable_vec),
    .intr_ack        (intr_ack     ),
    .uart_stop_sim   (uart_stop_sim)  
  );

  intr_gen u_intr_gen (
    .clk             (clk          ), 
    .rst_n           (rst_n        ),
    .INTR_INTVL      (intr_intvl   ),
    .intr_en         (intr_enable  ),
    .intr_ack        (intr_ack     ),  
    .irq_o           (irq_vec      )
  );

endmodule

