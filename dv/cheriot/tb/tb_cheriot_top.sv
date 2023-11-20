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
  input  logic [31:0]  instr_rdata_dii_i,
  output logic [31:0]  instr_pc_o,
  output logic         instr_ack_o
  );

  localparam MEM_AW = 14;

  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic [31:0] instr_rdata_mem;
  logic [6:0]  instr_rdata_intg;
  logic        instr_err;

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

  logic        irq_external;

  logic        cheri_pmode;
  logic        cheri_tsafe_en;

  // Memory map
  //   0x2000_0000 - 0x2000_ffff: instr_mem
  //   0x2001_0000 - 0x2001_ffff: data_mem
  //   0x2004_0000 - 0x2004_0fff: tsmap (shadow memory)
  //   0x2100_0600 - interrupt injection
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

  `ifdef MEM_RNDW
    assign mem_rndw = 1'b1;             // only a display flag
  `else
    assign mem_rndw = 1'b0;
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
 `endif // verilator

  ibex_top_tracing #(
                     .HeapBase        (32'h8000_0000),
                     .TSMapBase       (32'h8004_0000),
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
    .tsmap_cs_o           (),
    .tsmap_addr_o         (),
    .tsmap_rdata_i        (32'h0 ),
    .tsmap_rdata_intg_i   (7'h0),
    .mmreg_corein_i       (128'h0),
    .mmreg_coreout_o      (),
    .irq_software_i       (1'b0),
    .irq_timer_i          (1'b0        ),
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

  assign irq_external = 1'b0;

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
`ifdef DII_SIM 
  assign dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_rdata_dii = instr_rdata_dii_i;
  assign instr_ack_o = dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_ack;
  assign instr_pc_o = dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_pc;
  assign instr_rdata = 32'h0;

`else

  assign instr_rdata = instr_rdata_mem;
`endif  

  //
  // RAMs 
  //

  mem_model #(
    .MEM_AW    (MEM_AW),
    .MEM_DW    (32),
    .GNT_WMAX  (2),
    .RESP_WMAX (2)
  ) u_instr_mem (
    .clk             (clk_i         ), 
    .rst_n           (rstn_i        ),
    .data_req        (instr_req     ),
    .data_we         (1'b0      ),
    .data_be         (4'b1111       ),
    .data_addr       (instr_addr    ),
    .data_wdata      (32'h0   ),
    .data_gnt        (instr_gnt     ),
    .data_rvalid     (instr_rvalid  ),
    .data_rdata      (instr_rdata_mem),
    .data_err        (instr_err     )
  );

  mem_model #(
    .MEM_AW (MEM_AW),
    .MEM_DW    (33),
    .GNT_WMAX  (2),
    .RESP_WMAX (2)
  ) u_data_mem (
    .clk             (clk_i        ), 
    .rst_n           (rstn_i       ),
    .data_req        (data_req     ),
    .data_we         (data_we      ),
    .data_be         (data_be      ),
    .data_addr       (data_addr    ),
    .data_wdata      (data_wdata   ),
    .data_gnt        (data_gnt     ),
    .data_rvalid     (data_rvalid  ),
    .data_rdata      (data_rdata   ),
    .data_err        (data_err     )
  );

endmodule

