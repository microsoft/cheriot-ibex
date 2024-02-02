// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//`define BOOT_ADDR 32'h8000_0000
`define BOOT_ADDR 32'h8000_0000

import ibex_pkg::*;
import cheri_pkg::*;
import prim_ram_1p_pkg::*;

module tb_cheriot_top (
  input  logic         clk_i,
  input  logic         rstn_i,
  input  logic [31:0]  dii_insn_i,
  output logic [31:0]  dii_pc_o,
  output logic         dii_ack_o
  );

  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic [31:0] instr_rdata_mem;
  logic [6:0]  instr_rdata_intg;
  logic        instr_err;
  logic        instr_err_enable;

  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [32:0] data_wdata;
  logic [32:0] data_rdata;
  logic [6:0]  data_rdata_intg;
  logic        data_err;
  logic        data_err_enable;

  logic        irq_external;
  logic        irq_software;
  logic        irq_timer;
  logic [2:0]  irq_vec, intr_ack;
  logic        intr_enable;

  logic        cheri_pmode;
  logic        cheri_tsafe_en;

  logic        tsmap_cs;
  logic [15:0] tsmap_addr;
  logic [31:0] tsmap_rdata;

  logic [127:0] mmreg_corein;
  logic [63:0]  mmreg_coreout;

`ifndef VERILATOR
  `ifdef CHERI0
    defparam dut.u_ibex_top.CHERIoTEn = 1'b0;
    defparam dut.DataWidth = 32;
    localparam int unsigned busDataWidth = 32;
  `else
    defparam dut.u_ibex_top.CHERIoTEn = 1'b1;
    defparam dut.DataWidth = 33;
    localparam int unsigned busDataWidth = 33;
    defparam dut.u_ibex_top.u_ibex_core.cheri_tbre_wrapper_i.StkZIntrOK = 1;
  `endif

  `ifdef SECURE1
    defparam dut.u_ibex_top.SecureIbex = 1'b1;
    `ifndef CHERI0
      defparam dut.u_ibex_top.gen_lockstep.u_ibex_lockstep.u_shadow_core.cheri_tbre_wrapper_i.StkZIntrOK = 1;
    `endif
  `else
    defparam dut.u_ibex_top.SecureIbex = 1'b0;
  `endif

  `ifdef WBSTAGE0
    defparam dut.u_ibex_top.WritebackStage = 1'b0;
    assign rf_rd_a_hz = 1'b0;
    assign rf_rd_b_hz = 1'b0;
  `else
    defparam dut.u_ibex_top.WritebackStage = 1'b1;
    assign rf_rd_a_hz = dut.u_ibex_top.u_ibex_core.id_stage_i.gen_stall_mem.rf_rd_a_hz;
    assign rf_rd_b_hz = dut.u_ibex_top.u_ibex_core.id_stage_i.gen_stall_mem.rf_rd_b_hz;
  `endif  

  `ifdef MEMCAPFMT1
    defparam dut.u_ibex_top.MemCapFmt = 1'b1;
  `else
    defparam dut.u_ibex_top.MemCapFmt = 1'b0;
  `endif

  `ifdef CHERIPPLBC0
    defparam dut.u_ibex_top.CheriPPLBC = 1'b0;
  `else
    defparam dut.u_ibex_top.CheriPPLBC = 1'b1;
  `endif

  `ifdef CHERISBND21
    defparam dut.u_ibex_top.CheriSBND2 = 1'b1;
  `else
    defparam dut.u_ibex_top.CheriSBND2 = 1'b0;
  `endif

  `ifdef CHERITBRE0
    defparam dut.u_ibex_top.CheriTBRE = 1'b0;
    assign tbre_flag = 8'h00;
  `else
    defparam dut.u_ibex_top.CheriTBRE = 1'b1;
    assign tbre_flag = 8'h55;
  `endif

  `ifdef PMODE0
    assign cheri_pmode = 1'b0;
  `else
    assign cheri_pmode = 1'b1;
  `endif

  `ifdef TSAFE0 
    assign cheri_tsafe_en = 0;
  `else
    assign cheri_tsafe_en = 1;
  `endif

  `ifdef MULT_1CYCLE  
    defparam dut.u_ibex_top.u_ibex_core.RV32M = RV32MSingleCycle;
  `endif
   
  `ifdef BRANCH_PREDICT
    defparam dut.u_ibex_top.BranchPredictor = 1'b1;
  `endif

  `ifdef RV32B
    defparam dut.u_ibex_top.RV32B = 3;
  `endif
 `endif // ifndef verilator

  ibex_top_tracing #(
                     .HeapBase        (32'h8000_0000),
                     .TSMapBase       (32'h8003_0000),
                     .TSMapSize       (1024),
                     .DmHaltAddr      (`BOOT_ADDR + 'h40),
                     .DmExceptionAddr (`BOOT_ADDR + 'h44),
                     .MMRegDinW       (128),
                     .MMRegDoutW      (64)
  ) dut (
    .clk_i                (clk_i       ),
    .rst_ni               (rstn_i      ),
    .test_en_i            (1'b0        ),
    .scan_rst_ni          (1'b1        ),
    .ram_cfg_i            ('{0, 0}     ),
    .hart_id_i            ('0          ),
    .cheri_pmode_i        (cheri_pmode ),
    .cheri_tsafe_en_i     (cheri_tsafe_en ),
    .boot_addr_i          (`BOOT_ADDR  ), // align with spike boot address
    .debug_req_i          (1'b0        ),
    .fetch_enable_i       (4'b1001     ),
    .instr_req_o          (instr_req   ),
    .instr_gnt_i          (instr_gnt   ),
    .instr_rvalid_i       (instr_rvalid),
    .instr_addr_o         (instr_addr  ),
    .instr_rdata_i        (instr_rdata),
    .instr_rdata_intg_i   (instr_rdata_intg),
    .instr_err_i          (instr_err   ),
    .data_req_o           (data_req    ),
    .data_gnt_i           (data_gnt    ),
    .data_rvalid_i        (data_rvalid ),
    .data_we_o            (data_we     ),
    .data_be_o            (data_be     ),
    .data_addr_o          (data_addr   ),
    .data_wdata_o         (data_wdata),
    .data_rdata_i         (data_rdata),
    .data_rdata_intg_i    (data_rdata_intg),
    .data_err_i           (data_err    ),
    .tsmap_cs_o           (tsmap_cs),
    .tsmap_addr_o         (tsmap_addr),
    .tsmap_rdata_i        (tsmap_rdata),
    .tsmap_rdata_intg_i   (7'h0),
    .mmreg_corein_i       (mmreg_corein),
    .mmreg_coreout_o      (mmreg_coreout),
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
    .data_wdata_intg_o    (),
    .data_is_cap_o        ()
  );

  assign {irq_timer, irq_software,  irq_external} = irq_vec; 

  assign data_rdata_intg  = 7'h0;
  assign instr_rdata_intg = 7'h0;
  
  // detect internal alerts
  always @(posedge clk_i) begin

    if (dut.u_ibex_top.alert_major_internal_o | dut.u_ibex_top.alert_major_bus_o |
        dut.u_ibex_top.alert_minor_o) begin
      $display("Alert detected !!!!!!! @%t, major_int = %1b, major_bus = %1b, minor = %1b", $time,
               dut.u_ibex_top.alert_major_internal_o, dut.u_ibex_top.alert_major_bus_o, 
               dut.u_ibex_top.alert_minor_o);
    end
  end

  // waveform dump
`ifndef VERILATOR
  initial begin
    #0 $fsdbDumpfile("tb_cheriot_top.fsdb");
    $fsdbDumpvars(0, "+all", tb_cheriot_top); 
  end
`endif

  // push instructions to ID stage
  dii_if u_dii_if(
    .clk_i        (clk_i),
    .rstn_i       (rstn_i),
    .dii_insn_0_i (dii_insn_i),
    .dii_insn_1_i (32'h0),
    .dii_pc_o     (dii_pc_o),
    .dii_ack_0_o  (dii_ack_o),
    .dii_ack_1_o  ()
  );


`ifdef DII_SIM 
  assign instr_rdata = 32'h0;
`else
  assign instr_rdata = instr_rdata_mem;
`endif  

  logic [2:0] instr_err_rate, data_err_rate;
  logic [3:0] instr_gnt_wmax, data_gnt_wmax;
  logic [3:0] instr_resp_wmax, data_resp_wmax;
  logic [3:0] intr_intvl;
  logic [2:0] cap_err_rate;
  logic       cap_err_enable;
  logic [3:0] err_enable_vec;

  int unsigned cfg_instr_err_rate, cfg_data_err_rate;
  int unsigned cfg_instr_gnt_wmax, cfg_data_gnt_wmax;
  int unsigned cfg_instr_resp_wmax, cfg_data_resp_wmax;
  int unsigned cfg_intr_intvl;
  int unsigned cfg_cap_err_rate;

  //
  // simulation init
  //
  initial begin
    int i;

    // defaults
    instr_err_rate  = 3'h0;
    instr_gnt_wmax  = 4'h2;
    instr_resp_wmax = 4'h2;
    data_err_rate   = 3'h0;
    data_gnt_wmax   = 4'h2;
    data_resp_wmax  = 4'h2;
    intr_intvl      = 4'h0;
    cap_err_rate    = 3'h0;

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

    i = $value$plusargs("CAP_ERR_RATE=%d", cfg_cap_err_rate);
    if (i == 1) cap_err_rate = cfg_cap_err_rate[2:0];

    @(posedge rstn_i);
    repeat (10) @(posedge clk_i);    // wait after the hardware mtvec init
  end

  
  assign instr_err_enable = err_enable_vec[0];
  assign data_err_enable  = err_enable_vec[1];
  assign intr_enable      = err_enable_vec[2];
  assign cap_err_enable   = err_enable_vec[3];

  //
  // RAMs 
  //
  instr_mem_model u_instr_mem (
    .clk             (clk_i         ), 
    .rst_n           (rstn_i        ),
    .ERR_RATE        (instr_err_rate),
    .GNT_WMAX        (instr_gnt_wmax),
    .RESP_WMAX       (instr_resp_wmax),
    .err_enable      (instr_err_enable),
    .instr_req       (instr_req     ),
    .instr_addr      (instr_addr    ),
    .instr_gnt       (instr_gnt     ),
    .instr_rvalid    (instr_rvalid  ),
    .instr_rdata     (instr_rdata_mem),
    .instr_err       (instr_err     )
  );

  data_mem_model u_data_mem (
    .clk             (clk_i        ), 
    .rst_n           (rstn_i       ),
    .ERR_RATE        (data_err_rate),
    .GNT_WMAX        (data_gnt_wmax),
    .RESP_WMAX       (data_resp_wmax),
    .err_enable      (data_err_enable),
    .data_req        (data_req     ),
    .data_we         (data_we      ),
    .data_be         (data_be      ),
    .data_addr       (data_addr    ),
    .data_wdata      (data_wdata   ),
    .data_gnt        (data_gnt     ),
    .data_rvalid     (data_rvalid  ),
    .data_rdata      (data_rdata   ),
    .data_err        (data_err     ),
    .tsmap_cs        (tsmap_cs),
    .tsmap_addr      (tsmap_addr),
    .tsmap_rdata     (tsmap_rdata),
    .mmreg_corein    (mmreg_corein),
    .mmreg_coreout   (mmreg_coreout),
    .err_enable_vec  (err_enable_vec),
    .intr_ack        (intr_ack     )  
  );

  //
  // random interrupt generator
  //
  intr_gen u_intr_gen (
    .clk             (clk_i        ), 
    .rst_n           (rstn_i       ),
    .INTR_INTVL      (intr_intvl   ),
    .intr_en         (intr_enable  ),
    .intr_ack        (intr_ack     ),  
    .irq_o           (irq_vec      )
  );

  //
  // random cap error injection
  //
  cap_err_gen u_cap_err_gen ( 
    .clk             (clk_i        ),
    .rst_n           (rstn_i       ),
    .ERR_RATE        (cap_err_rate ),
    .err_enable      (cap_err_enable),
    .err_active      ( )
  );


endmodule

