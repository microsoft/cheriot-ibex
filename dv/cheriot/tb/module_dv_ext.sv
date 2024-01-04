// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "dv_fcov_macros.svh"

//
// extend internal modules for SVA & FCOV signals
//
module bindfiles;
  bind ibex_if_stage         ibex_if_stage_dv_ext    if_stage_dv_ext_i (.*);
  bind ibex_controller       ibex_controller_dv_ext  controller_dv_ext_i (.*);
  bind ibex_load_store_unit  ibex_lsu_dv_ext         lsu_dv_ext_i (.*);
  bind cheri_ex              cheri_ex_dv_ext         cheri_ex_dv_ext_i (.*);
  bind ibex_core             ibex_core_dv_ext        ibex_core_dv_ext_i (.*);
  bind ibex_top              ibex_top_dv_ext         ibex_top_dv_ext_i (.*);
endmodule


////////////////////////////////////////////////////////////////
// ibex_if_stage
////////////////////////////////////////////////////////////////
module ibex_if_stage_dv_ext (
  input  logic                  clk_i,
  input  logic                  rst_ni
);

  `DV_FCOV_SIGNAL_GEN_IF(logic [1:0], dummy_instr_type,
    gen_dummy_instr.dummy_instr_i.lfsr_data.instr_type, if_stage_i.DummyInstructions)
  `DV_FCOV_SIGNAL_GEN_IF(logic, insert_dummy_instr,
    gen_dummy_instr.insert_dummy_instr, if_stage_i.DummyInstructions)

endmodule

////////////////////////////////////////////////////////////////
// ibex_controller
////////////////////////////////////////////////////////////////
module ibex_controller_dv_ext import ibex_pkg::*; (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  debug_req_i,
  input  logic                  debug_mode_q,
  input  logic                  debug_single_step_i,
  input  logic                  do_single_step_d,
  input  logic                  do_single_step_q,
  input  ctrl_fsm_e             ctrl_fsm_cs,
  input  ctrl_fsm_e             ctrl_fsm_ns
);

  `DV_FCOV_SIGNAL(logic, all_debug_req, debug_req_i || debug_mode_q || debug_single_step_i)
  `DV_FCOV_SIGNAL(logic, debug_wakeup, (ctrl_fsm_cs == SLEEP) & (ctrl_fsm_ns == FIRST_FETCH) &
                                        (debug_req_i || debug_mode_q || debug_single_step_i))
  `DV_FCOV_SIGNAL(logic, interrupt_taken, (ctrl_fsm_cs != IRQ_TAKEN) & (ctrl_fsm_ns == IRQ_TAKEN))
  `DV_FCOV_SIGNAL(logic, debug_entry_if,
      (ctrl_fsm_cs != DBG_TAKEN_IF) & (ctrl_fsm_ns == DBG_TAKEN_IF))
  `DV_FCOV_SIGNAL(logic, debug_entry_id,
      (ctrl_fsm_cs != DBG_TAKEN_ID) & (ctrl_fsm_ns == DBG_TAKEN_ID))
  `DV_FCOV_SIGNAL(logic, pipe_flush, (ctrl_fsm_cs != FLUSH) & (ctrl_fsm_ns == FLUSH))
  `DV_FCOV_SIGNAL(logic, debug_req, debug_req_i & ~debug_mode_q)
  `DV_FCOV_SIGNAL(logic, debug_single_step_taken, do_single_step_d & ~do_single_step_q)

endmodule


////////////////////////////////////////////////////////////////
// ibex_load_store_unit
////////////////////////////////////////////////////////////////
module ibex_lsu_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         lsu_req_i,
  input  logic         data_req_o,
  input  logic         addr_incr_req_o,
  input  logic         data_rvalid_i,
  input  logic [1:0]   lsu_type_i,
  input  logic [1:0]   data_offset,
  input  logic [1:0]   rdata_offset_q,
  input  logic [1:0]   data_type_q,
  input  logic [31:0]  data_addr_o,
  input  ls_fsm_e      ls_fsm_cs,
  input  logic         busy_o,
  input  logic         data_err_i,
  input  logic         load_err_o,
  input  logic         store_err_o,
  input  logic         pmp_err_q,
  input  logic         data_pmp_err_i,
  input  logic         cheri_err_q,
  input  logic         resp_is_tbre_q

);
  // Set when awaiting the response for the second half of a misaligned access
  logic fcov_mis_2_en_d, fcov_mis_2_en_q;

  // fcov_mis_rvalid_1: Set when the response is received to the first half of a misaligned access,
  // fcov_mis_rvalid_2: Set when response is received for the second half
  logic fcov_mis_rvalid_1, fcov_mis_rvalid_2;

  // Set when the first half of a misaligned access saw a bus errror
  logic fcov_mis_bus_err_1_d, fcov_mis_bus_err_1_q;

  assign fcov_mis_rvalid_1 = ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE} &&
                                data_rvalid_i;

  assign fcov_mis_rvalid_2 = ls_fsm_cs inside {IDLE} && fcov_mis_2_en_q && data_rvalid_i;

  assign fcov_mis_2_en_d = fcov_mis_rvalid_2 ? 1'b0            :  // clr
                           fcov_mis_rvalid_1 ? 1'b1            :  // set
                                               fcov_mis_2_en_q ;

  assign fcov_mis_bus_err_1_d = fcov_mis_rvalid_2                   ? 1'b0                 : // clr
                                fcov_mis_rvalid_1 && data_err_i ? 1'b1                 : // set
                                                                      fcov_mis_bus_err_1_q ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fcov_mis_2_en_q <= 1'b0;
      fcov_mis_bus_err_1_q <= 1'b0;
    end else begin
      fcov_mis_2_en_q <= fcov_mis_2_en_d;
      fcov_mis_bus_err_1_q <= fcov_mis_bus_err_1_d;
    end
  end

  `DV_FCOV_SIGNAL(logic, ls_error_exception, (load_err_o | store_err_o) & ~pmp_err_q & ~cheri_err_q)
  `DV_FCOV_SIGNAL(logic, ls_pmp_exception, (load_err_o | store_err_o) & pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_cheri_exception, (load_err_o | store_err_o) & cheri_err_q)

  `DV_FCOV_SIGNAL(logic, ls_first_req, lsu_req_i & (ls_fsm_cs == IDLE))
  `DV_FCOV_SIGNAL(logic, ls_second_req,
    (ls_fsm_cs inside {WAIT_RVALID_MIS}) & data_req_o & addr_incr_req_o)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_1,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_GNT_MIS}) && pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_2,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE}) && data_pmp_err_i)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexDataTypeKnown, (lsu_req_i | busy_o) |-> !$isunknown(lsu_type_i))
  `ASSERT(IbexDataOffsetKnown, (lsu_req_i | busy_o) |-> !$isunknown(data_offset))
  `ASSERT_KNOWN(IbexRDataOffsetQKnown, rdata_offset_q)
  `ASSERT_KNOWN(IbexDataTypeQKnown, data_type_q)
  `ASSERT(IbexLsuStateValid, ls_fsm_cs inside {
      IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT,
      WAIT_RVALID_MIS_GNTS_DONE, 
      CTX_WAIT_GNT1, CTX_WAIT_GNT2, CTX_WAIT_RESP})

  // Address must not contain X when request is sent.
  `ASSERT(IbexDataAddrUnknown, data_req_o |-> !$isunknown(data_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexDataAddrUnaligned, data_req_o |-> (data_addr_o[1:0] == 2'b00))

endmodule


////////////////////////////////////////////////////////////////
// cheri_ex
////////////////////////////////////////////////////////////////

module cheri_ex_dv_ext (
  input  logic                  clk_i,
  input  logic                  rst_ni
  );

endmodule

////////////////////////////////////////////////////////////////
// ibex_core
////////////////////////////////////////////////////////////////

module ibex_core_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        cheri_pmode_i,
  input  logic        cheri_tsafe_en_i,
  input  logic        cheri_exec_id,
  input  logic        rf_we_lsu,
  input  logic [35:0] cheri_operator,
  input  logic        csr_op_en,
  input  logic        instr_done_wb,
  input  logic        outstanding_load_wb,
  input  logic        outstanding_store_wb
  );

  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;
  logic cheri_intl_clbc;

  assign outstanding_load_id  = (id_stage_i.instr_executing & (id_stage_i.lsu_req_dec & ~id_stage_i.lsu_we)) |
                                (cheri_exec_id & cheri_operator[CLOAD_CAP]);
  assign outstanding_store_id = (id_stage_i.instr_executing & id_stage_i.lsu_req_dec & id_stage_i.lsu_we) |
                                (cheri_exec_id & cheri_operator[CSTORE_CAP]);
  assign cheri_intl_clbc = cheri_operator[CLOAD_CAP] & ~u_ibex_core.CheriPPLBC & cheri_tsafe_en_i;

  if (u_ibex_core.WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & (load_store_unit_i.split_misaligned_access | cheri_intl_clbc));

    assign outstanding_store_resp = outstanding_store_wb |
      (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu  |-> outstanding_load_wb, clk_i, !rst_ni)
  end else begin : gen_no_wb_stage
    // Without writeback stage only look into whether load or store is in ID to determine if
    // a response is expected.
    assign outstanding_load_resp  = outstanding_load_id;
    assign outstanding_store_resp = outstanding_store_id;

    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_resp, clk_i, !rst_ni)
  end
  
  if (~u_ibex_core.CheriTBRE) begin
  `ASSERT(NoMemResponseWithoutPendingAccess,
    // this doesn't work for CLC since 1st data_rvalid comes back before wb
    // data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp,  clk_i, !rst_ni)
    load_store_unit_i.lsu_resp_valid_o |-> outstanding_load_resp | outstanding_store_resp,  clk_i, !rst_ni)
  end

  if (u_ibex_core.CHERIoTEn) begin : gen_cheri_assert
    // decoded cheri_operator should be one-hot
    `ASSERT(CheriOperatorOneHotOnly, $onehot0(cheri_operator))

    // cheri_ex operand forwarding logic should behave the same as ID_stage
    `ASSERT_IF(CheriFwdCheckA, (g_cheri_ex.u_cheri_ex.rf_rdata_ng_a == id_stage_i.rf_rdata_a_fwd), id_stage_i.instr_executing)
    `ASSERT_IF(CheriFwdCheckB, (g_cheri_ex.u_cheri_ex.rf_rdata_ng_b == id_stage_i.rf_rdata_b_fwd), id_stage_i.instr_executing)

    if (u_ibex_core.WritebackStage && ~u_ibex_core.CheriPPLBC) begin
    // cheri_ex state machines must be in IDLE state when a new instruction starts
    `ASSERT(CheriLsuFsmIdle1, instr_id_done |-> (load_store_unit_i.ls_fsm_ns == 0), clk_i, !rst_ni)
    `ASSERT(CheriLsuFsmIdle2, ((load_store_unit_i.ls_fsm_cs == 0) && load_store_unit_i.lsu_req_i)  |->
           ((load_store_unit_i.cap_rx_fsm_q==0) | (load_store_unit_i.cap_rx_fsm_q==2)), clk_i, !rst_ni)
    `ASSERT_IF(CheriLsuFsmWaitResp, (load_store_unit_i.cap_rx_fsm_q != 7), 1'b1)
    end

    // only writes to regfile when wb_done
    if (u_ibex_core.WritebackStage) begin
      `ASSERT(CheriWrRegs, u_ibex_core.rf_we_wb |-> instr_done_wb, clk_i, !rst_ni)
    end
  end
 
  // These assertions are in top-level as instr_valid_id required as the enable term
  `ASSERT(IbexCsrOpValid, u_ibex_core.instr_valid_id |-> u_ibex_core.csr_op inside {
      CSR_OP_READ,
      CSR_OP_WRITE,
      CSR_OP_SET,
      CSR_OP_CLEAR
      })
  `ASSERT_KNOWN_IF(IbexCsrWdataIntKnown, cs_registers_i.csr_wdata_int, csr_op_en)

  // Functional coverage signals
  `DV_FCOV_SIGNAL(logic, csr_read_only,
      (u_ibex_core.csr_op == CSR_OP_READ) && u_ibex_core.csr_access && (csr_op_en || u_ibex_core.illegal_insn_id))
  `DV_FCOV_SIGNAL(logic, csr_write,
      cs_registers_i.csr_wr && u_ibex_core.csr_access && (csr_op_en || u_ibex_core.illegal_insn_id))

  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_a_id, gen_regfile_ecc.rf_ecc_err_a_id, u_ibex_core.RegFileECC)
  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_b_id, gen_regfile_ecc.rf_ecc_err_b_id, u_ibex_core.RegFileECC)

endmodule

////////////////////////////////////////////////////////////////
// ibex_top
////////////////////////////////////////////////////////////////

module ibex_top_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        test_en_i,     // enable all clock gates for testing
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input  logic        cheri_pmode_i,
  input  logic        cheri_tsafe_en_i,
  input  logic [31:0] hart_id_i,
  input  logic [31:0] boot_addr_i,

  input  logic        instr_req_o,
  input  logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic [6:0]  instr_rdata_intg_i,
  input  logic        instr_gnt_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i,
  input  logic        data_req_o,
  input  logic        data_is_cap_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  input  logic        data_we_o,
  input  logic [3:0]  data_be_o,
  input  logic [31:0] data_addr_o,
  input  logic [32:0] data_wdata_o,
  input  logic [6:0]  data_wdata_intg_o,
  input  logic [32:0] data_rdata_i,
  input  logic [6:0]  data_rdata_intg_i,
  input  logic        data_err_i,
  input  logic        debug_req_i,
  input  logic        irq_software_i,
  input  logic        irq_timer_i,
  input  logic        irq_external_i,
  input  logic [14:0] irq_fast_i,
  input  logic        irq_nm_i,       // non-maskeable interrupt
  input  fetch_enable_t  fetch_enable_i,
  input  logic        core_sleep_o
);

  // X check for top-level input s
  `ASSERT_KNOWN(IbexInstrReqX, instr_req_o)
  `ASSERT_KNOWN_IF(IbexInstrReqPayloadX, instr_addr_o, instr_req_o)

  `ASSERT_KNOWN(IbexDataReqX, data_req_o)
  `ASSERT_KNOWN_IF(IbexDataReqPayloadX,
    {data_we_o, data_be_o, data_addr_o, data_wdata_o, data_wdata_intg_o}, data_req_o)

  `ASSERT_KNOWN(IbexCoreSleepX, core_sleep_o)

  // X check for top-level inputs
  `ASSERT_KNOWN(IbexTestEnX, test_en_i)
  `ASSERT_KNOWN(IbexRamCfgX, ram_cfg_i)
  `ASSERT_KNOWN(IbexHartIdX, hart_id_i)
  `ASSERT_KNOWN(IbexBootAddrX, boot_addr_i)

  `ASSERT_KNOWN(IbexInstrGntX, instr_gnt_i)
  `ASSERT_KNOWN(IbexInstrRValidX, instr_rvalid_i)
  `ASSERT_KNOWN_IF(IbexInstrRPayloadX,
    {instr_rdata_i, instr_rdata_intg_i, instr_err_i}, instr_rvalid_i)

  `ASSERT_KNOWN(IbexDataGntX, data_gnt_i)
  `ASSERT_KNOWN(IbexDataRValidX, data_rvalid_i)
  
  // kliu - check data_rdata_i for reads only (FPGA ram model drives rdata for writes also)
  logic [3:0]  data_be_q;
  logic [32:0] data_strb;

  assign data_strb = {|data_be_q, {8{data_be_q[3]}}, {8{data_be_q[2]}}, {8{data_be_q[1]}}, {8{data_be_q[0]}}} & 
                     {33{~u_ibex_core.load_store_unit_i.data_we_q}};
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) data_be_q <= 4'h0;
    else if (data_req_o && data_gnt_i) data_be_q <= data_be_o;
  end
  
  `ASSERT_KNOWN_IF(IbexDataRPayloadX, {(data_strb & data_rdata_i), 
    ({7{~u_ibex_core.load_store_unit_i.data_we_q}} & data_rdata_intg_i), data_err_i}, data_rvalid_i)

  `ASSERT_KNOWN(IbexIrqX, {irq_software_i, irq_timer_i, irq_external_i, irq_fast_i, irq_nm_i})

  `ASSERT_KNOWN(IbexScrambleKeyValidX, u_ibex_top.scramble_key_valid_i)
  `ASSERT_KNOWN_IF(IbexScramblePayloadX, {u_ibex_top.scramble_key_i, u_ibex_top.scramble_nonce_i}, u_ibex_top.scramble_key_valid_i)

  `ASSERT_KNOWN(IbexDebugReqX, debug_req_i)
  `ASSERT_KNOWN(IbexFetchEnableX, fetch_enable_i)

endmodule
