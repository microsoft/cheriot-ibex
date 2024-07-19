`define BOOT_ADDR 32'h8000_0000

module core_ibex_testrig_tb_top;
  import ibex_pkg::*;
  import cheri_pkg::*;

  wire clk;
  wire rst_n;
  logic clk_dly;

  clk_rst_if clk_if(.clk(clk), .rst_n(rst_n));
  core_ibex_rvfi_if rvfi_if(.clk(clk));
  core_ibex_dii_intf dii_if(.clk(clk_dly), .rst_n(rst_n), .rvfi_valid(dut.rvfi_valid));

  // need to figure out a better way to do this - this is just to make sure instr_ack is sampled 
  // and dii_instr is updated right before the clk rising edge (after the ID stage instruction
  // retirement decision is made by RTL

  always @(clk) begin
    clk_dly <= #15 clk;
  end

  logic instr_req;
  logic instr_gnt;
  logic instr_rvalid;

  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [32:0] data_wdata;
  logic [32:0] data_rdata;
  logic [6:0]  data_rdata_intg;
  logic        data_is_cap;
  logic        data_err;

  logic        tsmap_cs;
  logic [15:0] tsmap_addr;
  logic [31:0] tsmap_rdata;


  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      instr_rvalid <= 1'b0;
    end else begin
      instr_rvalid <= instr_req;
    end
  end

  assign instr_gnt = instr_req;

  ibex_top_tracing #(
                     .HeapBase        (32'h8000_0000), // Base of memory.
                     .TSMapBase       (32'h8300_0000), // Same as Sail.
                     .TSMapSize       (4096), // Cover all of memory.
                     .DmHaltAddr      (`BOOT_ADDR + 'h40),
                     .DmExceptionAddr (`BOOT_ADDR + 'h44),
                     .MMRegDinW       (128),
                     .MMRegDoutW      (64)
  ) dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),
    .test_en_i            (1'b0),
    .scan_rst_ni          (1'b1),
    .ram_cfg_i            ('{0, 0}),
    .hart_id_i            ('0),
    .cheri_pmode_i        (1'b1),
    .cheri_tsafe_en_i     (1'b0),
    .boot_addr_i          (`BOOT_ADDR), // align with spike boot address
    .debug_req_i          (1'b0),
    .fetch_enable_i       (4'b1001),
    .instr_req_o          (instr_req),
    .instr_gnt_i          (instr_gnt),
    .instr_rvalid_i       (instr_rvalid),
    .instr_addr_o         (),
    .instr_rdata_i        ('0),
    .instr_rdata_intg_i   ('0),
    .instr_err_i          (1'b0),
    .data_req_o           (data_req),
    .data_gnt_i           (data_gnt),
    .data_rvalid_i        (data_rvalid),
    .data_we_o            (data_we),
    .data_be_o            (data_be),
    .data_is_cap_o        (data_is_cap),
    .data_addr_o          (data_addr),
    .data_wdata_o         (data_wdata),
    .data_rdata_i         (data_rdata),
    .data_rdata_intg_i    ('0),
    .data_err_i           (data_err),
    .tsmap_cs_o           (tsmap_cs),
    .tsmap_addr_o         (tsmap_addr),
    .tsmap_rdata_i        (tsmap_rdata),
    .tsmap_rdata_intg_i   ('0),
    .mmreg_corein_i       ('0),
    .mmreg_coreout_o      (),
    .irq_software_i       ('0),
    .irq_timer_i          ('0),
    .irq_external_i       ('0),
    .irq_fast_i           (15'h0),
    .irq_nm_i             (1'b0),
    .scramble_key_valid_i (1'b0),
    .scramble_key_i       (128'h0),
    .scramble_nonce_i     (64'h0),
    .core_sleep_o         (),
    .double_fault_seen_o  (),
    .crash_dump_o         (),
    .scramble_req_o       (),
    .data_wdata_intg_o    ()
  );

  data_mem_model u_data_mem (
    .clk             (clk        ), 
    .rst_n           (rst_n       ),
    .data_req        (data_req     ),
    .data_we         (data_we      ),
    .data_be         (data_be      ),
    .data_is_cap     (data_is_cap  ),
    .data_addr       (data_addr    ),
    .data_wdata      (data_wdata   ),
    .data_gnt        (data_gnt     ),
    .data_rvalid     (data_rvalid  ),
    .data_rdata      (data_rdata   ),
    .data_err        (data_err),
    .tsmap_cs        (tsmap_cs),
    .tsmap_addr      (tsmap_addr),
    .tsmap_rdata     (tsmap_rdata)
  );


  assign rvfi_if.reset         = ~rst_n;
  assign rvfi_if.valid         = dut.rvfi_valid;
  assign rvfi_if.order         = dut.rvfi_order;
  assign rvfi_if.insn          = dut.rvfi_insn;
  assign rvfi_if.trap          = dut.rvfi_trap;
  assign rvfi_if.intr          = dut.rvfi_intr;
  assign rvfi_if.mode          = dut.rvfi_mode;
  assign rvfi_if.ixl           = dut.rvfi_ixl;
  assign rvfi_if.rs1_addr      = dut.rvfi_rs1_addr;
  assign rvfi_if.rs2_addr      = dut.rvfi_rs2_addr;
  assign rvfi_if.rs1_rdata     = dut.rvfi_rs1_rdata;
  assign rvfi_if.rs2_rdata     = dut.rvfi_rs2_rdata;
  assign rvfi_if.rd_addr       = dut.rvfi_rd_addr;
  assign rvfi_if.rd_wdata      = dut.rvfi_rd_wdata;
  assign rvfi_if.pc_rdata      = dut.rvfi_pc_rdata;
  assign rvfi_if.pc_wdata      = dut.rvfi_pc_wdata;
  assign rvfi_if.mem_addr      = dut.rvfi_mem_addr;
  assign rvfi_if.mem_rmask     = dut.rvfi_mem_rmask;
  assign rvfi_if.mem_rdata     = dut.rvfi_mem_rdata;
  assign rvfi_if.mem_wdata     = dut.rvfi_mem_wdata;
  assign rvfi_if.ext_mip       = dut.rvfi_ext_mip;
  assign rvfi_if.ext_nmi       = dut.rvfi_ext_nmi;
  assign rvfi_if.ext_debug_req = dut.rvfi_ext_debug_req;
  assign rvfi_if.ext_mcycle    = dut.rvfi_ext_mcycle;

  `define IBEX_DII_INSN_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_rdata_dii
  `define IBEX_DII_ACK_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.instr_ack

 // assign dii_if.instr_ack = `IBEX_DII_ACK_PATH & ~dut.u_ibex_top.u_ibex_core.if_stage_i.pc_set_i;
  logic exc_req_d, exc_req_wb;
  logic instr_done;
  logic if_instr_valid;
  ctrl_fsm_e ctrl_fsm_ns;

  assign exc_req_d = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.exc_req_d;
  assign exc_req_wb = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.exc_req_wb;
  assign ctrl_fsm_ns = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.ctrl_fsm_ns;
  assign instr_done = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_done;
  assign if_instr_valid = dut.u_ibex_top.u_ibex_core.if_stage_i.if_instr_valid;

  // probably delay and line up with ctrl_fsm_cs instead?
  // also - this only control instruction update, do NOT qualify with if_instr_valid
  assign dii_if.instr_ack = (exc_req_d && ~exc_req_wb && (ctrl_fsm_ns == FLUSH)) || instr_done;

  // initilizing ibex regfile/CSR to match sail by forcing for now
  initial begin
    int i;

    while (1) begin
      @(posedge rst_n);    // handle multipe-reset case

      for (i = 1; i < 16; i++)
        force dut.u_ibex_top.gen_regfile_cheriot.register_file_i.rf_cap_q[i] = MTDC_RESET_CAP;
            
      force dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mepc_csr.rdata_q[31:0] = 32'h8000_0000;
      //force dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mstatus_csr.rdata_q[5:0] = 6'b101100;  //priv_lvl_m
      // cheriot-sail configuration doesn't support PRIV_LVL_U
      force dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mstatus_csr.rdata_q[3:2] = 2'b11;

      @(posedge clk);
      @(posedge clk);
      for (i = 1; i < 16; i++)
        release dut.u_ibex_top.gen_regfile_cheriot.register_file_i.rf_cap_q[i];

      release dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mepc_csr.rdata_q[31:0];
      //release dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mstatus_csr.rdata_q[5:0];
    end 

  end

  assign `IBEX_DII_INSN_PATH = dii_if.instr_rdata_dii;

  initial begin
    clk_if.set_active();

    fork
      clk_if.apply_reset(.reset_width_clks (100));
    join_none

    uvm_config_db#(virtual clk_rst_if)::set(null, "*", "clk_if", clk_if);
    uvm_config_db#(virtual core_ibex_dii_intf)::set(null, "*", "dii_if", dii_if);
    uvm_config_db#(virtual core_ibex_rvfi_if)::set(null, "*", "rvfi_if", rvfi_if);

    run_test();
  end
endmodule
