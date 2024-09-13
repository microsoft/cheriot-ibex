// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

//
// extend internal modules for SVA & FCOV signals
//
module bindfiles;
  bind ibex_if_stage         ibex_if_stage_dv_ext      if_stage_dv_ext_i (.*);
  bind ibex_id_stage         ibex_id_stage_dv_ext      id_stage_dv_ext_i (.*);
  bind ibex_controller       ibex_controller_dv_ext    controller_dv_ext_i (.*);
  bind ibex_load_store_unit  ibex_lsu_dv_ext           lsu_dv_ext_i (.*);
  bind cheri_ex              cheri_ex_dv_ext           cheri_ex_dv_ext_i (.*);
  bind cheri_trvk_stage      cheri_trvk_stage_dv_ext   trvk_dv_ext_i (.*);
  bind cheri_tbre_wrapper    cheri_tbre_wrapper_dv_ext tbre_wrapper_dv_ext_i (.*);
  bind cheri_tbre            cheri_tbre_dv_ext         tbre_dv_ext_i (.*);
  bind cheri_stkz            cheri_stkz_dv_ext         stkz_dv_ext_i (.*);
  bind ibex_cs_registers     ibex_cs_registers_dv_ext  cs_reg_dv_ext_i (.*);
  bind ibex_core             ibex_core_dv_ext          ibex_core_dv_ext_i (.*);
  bind ibex_top              ibex_top_dv_ext           ibex_top_dv_ext_i (.*);
endmodule


////////////////////////////////////////////////////////////////
// ibex_if_stage
////////////////////////////////////////////////////////////////

module ibex_if_stage_dv_ext import cheri_pkg::*; import cheriot_dv_pkg::*; (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  if_instr_valid,
  input  logic [31:0]           pc_if_o,
  input  pcc_cap_t              pcc_cap_i
);

  logic fcov_pending_fetch_bound_vio;

  `DV_FCOV_SIGNAL_GEN_IF(logic [1:0], dummy_instr_type,
    gen_dummy_instr.dummy_instr_i.lfsr_data.instr_type, if_stage_i.DummyInstructions)
  `DV_FCOV_SIGNAL_GEN_IF(logic, insert_dummy_instr,
    gen_dummy_instr.insert_dummy_instr, if_stage_i.DummyInstructions)

   assign fcov_pending_fetch_bound_vio = ~if_instr_valid & ~is_representable(pcc2fullcap(pcc_cap_i), pc_if_o);

endmodule

////////////////////////////////////////////////////////////////
// ibex_id_stage
////////////////////////////////////////////////////////////////

module ibex_id_stage_dv_ext import ibex_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic [31:0] rf_reg_rdy_i,
  input  logic        rf_ren_a,
  input  logic        rf_ren_a_dec,
  input  logic [4:0]  rf_raddr_a_o,
  input  logic        rf_ren_b,
  input  logic        rf_ren_b_dec,
  input  logic [4:0]  rf_raddr_b_o,
  input  logic        rf_we_id_o,
  input  logic        rf_we_dec,
  input  logic [4:0]  rf_waddr_id_o,
  input  logic        cheri_exec_id_o,
  input  logic        instr_executing,
  input  logic        instr_valid_i,
  input  logic        instr_fetch_err_i,
  input  logic        illegal_insn_o,
  input  logic        instr_is_legal_cheri
);

  logic [2:0] fcov_trvk_stall_cause;

  assign fcov_trvk_stall_cause[0] = rf_ren_a && ~rf_reg_rdy_i[rf_raddr_a_o];
  assign fcov_trvk_stall_cause[1] = rf_ren_b && ~rf_reg_rdy_i[rf_raddr_b_o];
  assign fcov_trvk_stall_cause[2] = rf_we_id_o && ~rf_reg_rdy_i[rf_waddr_id_o]; 

  // cheri_exec_id is included in instr_executing
  `ASSERT(IbexExecInclCheri, (cheri_exec_id_o |-> instr_executing))
  `ASSERT(IbexLegalCheri, (instr_is_legal_cheri |-> ~illegal_insn_o))

  // rf_we_dec is now a superset of cheri_rf_we_dec
  `ASSERT(IbexCheriRfWe, ((decoder_i.cheri_rf_we_dec & ~decoder_i.illegal_insn_o) |-> rf_we_dec))


  // rf_ren_x is directly gated by illegal_insn in RTL, no need to prove here.
  // assign rf_ren_a = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_a_dec;
  // assign rf_ren_b = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_b_dec;

  // Let's use formal tool to prove rf_ren_x matches alu_op_x_mux_sel. 
  logic fcov_rf_ren_a, fcov_rf_ren_b;

  logic no_ren_a_case1, no_ren_a_case2;
  assign no_ren_a_case1 = (decoder_i.opcode == OPCODE_SYSTEM) & 
                         ((decoder_i.instr[14] == 1'b1) | (decoder_i.instr[14:12] == 3'b000));
  assign no_ren_a_case2 = (decoder_i.opcode == OPCODE_MISC_MEM);  
 
  assign fcov_rf_ren_a = ((decoder_i.alu_op_a_mux_sel_o == OP_A_REG_A) & ~no_ren_a_case1 & ~no_ren_a_case2) | 
                         (decoder_i.cheri_rf_ren_a & decoder_i.cheri_opcode_en & ~decoder_i.illegal_c_insn_i) |
                         ((decoder_i.opcode == OPCODE_AUICGP) & ~decoder_i.illegal_c_insn_i) |
                         (decoder_i.opcode == OPCODE_JALR) |
                         (decoder_i.opcode == OPCODE_BRANCH);
  assign fcov_rf_ren_b = (decoder_i.alu_op_b_mux_sel_o == OP_B_REG_B) | 
                         (decoder_i.cheri_rf_ren_b & decoder_i.cheri_opcode_en & ~decoder_i.illegal_c_insn_i) |
                         (decoder_i.opcode == OPCODE_STORE);
 
  `ASSERT(IbexRfRenA, (rf_ren_a_dec == fcov_rf_ren_a))
  // alu_op_b_mux_sel in branch cases has instr_valid_i term, not purely from decoding
  `ASSERT(IbexRfRenB, ((rf_ren_b_dec & instr_valid_i) == (fcov_rf_ren_b & instr_valid_i)))

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
  input  ctrl_fsm_e             ctrl_fsm_ns,
  input  logic                  flush_id,
  input  logic                  pc_set_o,
  input  pc_sel_e               pc_mux_o,
  input  logic                  special_req,
  input  logic                  special_req_pc_change,
  input  logic                  handle_irq,
  input  logic                  enter_debug_mode,
  input  logic                  id_in_ready_o,
  input  logic                  ready_wb_i,
  input  exc_pc_sel_e           exc_pc_mux_o,
  input  logic                  cheri_wb_err_i,
  input  logic                  instr_valid_i
);

  `DV_FCOV_SIGNAL(logic, all_debug_req, debug_req_i || debug_mode_q || debug_single_step_i)
  `DV_FCOV_SIGNAL(logic, debug_wakeup, (ctrl_fsm_cs == SLEEP) & (ctrl_fsm_ns == FIRST_FETCH) &
                                        (debug_req_i || debug_mode_q || debug_single_step_i))
  `DV_FCOV_SIGNAL(logic, interrupt_taken, (ctrl_fsm_cs != IRQ_TAKEN) & (ctrl_fsm_ns == IRQ_TAKEN))
  `DV_FCOV_SIGNAL(logic, debug_entry_if,
      (ctrl_fsm_cs != DBG_TAKEN_IF) & (ctrl_fsm_ns == DBG_TAKEN_IF))
  `DV_FCOV_SIGNAL(logic, debug_entry_id,
      (ctrl_fsm_cs != DBG_TAKEN_ID) & (ctrl_fsm_ns == DBG_TAKEN_ID))

   //  `DV_FCOV_SIGNAL(logic, pipe_flush, (ctrl_fsm_cs != FLUSH) & (ctrl_fsm_ns == FLUSH))
   // QQQ flush_id aligns with instr_unstalled
  `DV_FCOV_SIGNAL(logic, pipe_flush, flush_id)
  `DV_FCOV_SIGNAL(logic, debug_req, debug_req_i & ~debug_mode_q)
  `DV_FCOV_SIGNAL(logic, debug_single_step_taken, do_single_step_d & ~do_single_step_q)

   // signal used by testbench to see if CPU is executing an exception/intrrupt handler
   logic cpu_in_isr;
   logic irq_pending;
   logic fcov_irq_miss;

   always @(posedge clk_i, negedge rst_ni) begin
     if (~rst_ni) begin
       cpu_in_isr <= 1'b0;
       irq_pending <= 1'b0;
     end else begin 
       if (((ctrl_fsm_cs == FLUSH) && pc_set_o && (pc_mux_o == PC_EXC)) ||
           (ctrl_fsm_cs == IRQ_TAKEN))
         cpu_in_isr <= 1'b1;
       else if ((ctrl_fsm_cs == FLUSH) && pc_set_o && (pc_mux_o == PC_ERET))
         cpu_in_isr <= 1'b0;

       irq_pending <= (ctrl_fsm_cs == DECODE) && handle_irq && id_stage_i.instr_done;
     end

   end

  // IRQ must be taken if unmasked interrupt at the end of current instruction unless irq goes away..
  // this is for coverage.
  assign fcov_irq_miss = irq_pending & ~handle_irq;

   //
   // CHERIoT assertions
   //
    `ASSERT(CHERI_WB_FAULT, (cheri_wb_err_i |=> (ctrl_fsm_cs == FLUSH)))

   //
   // Assertions moved from the ibex_controller.sv RTL to here
   //
 
  // Selectors must be known/valid.
  `ASSERT(IbexCtrlStateValid, ctrl_fsm_cs inside {
      RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
      IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID})
   

  // Interrupt are taken in 3 sequential steps
  //   - DECODE, handle_irq (unmasked interrupts) and no special_req. 
  //     halt_if and wait for current ID instr done
  //   - instr_valid  = 0. 
  //     -- Note at this step if mie is cleared by the ID instr, handle_irq goes asway and we 
  //        stay in DECODE
  //   - ctrl_fsm_cs = IRQ_TAKEN, set PC
  logic go_take_irq, ready_for_irq;
  assign ready_for_irq = (ctrl_fsm_cs == DECODE) && handle_irq && ~special_req &&
                          ~enter_debug_mode && id_stage_i.instr_done;
  assign go_take_irq = (ctrl_fsm_cs == DECODE) && handle_irq && ~special_req &&
                       ~enter_debug_mode && ~instr_valid_i & ready_wb_i;

  `ASSERT(IbexIrqReady, (ready_for_irq |=> ~instr_valid_i))
  `ASSERT(IbexIrqTaken, (go_take_irq |-> (ctrl_fsm_ns == IRQ_TAKEN)))

  `ASSERT(IbexIrqTakenInvalid, ((ctrl_fsm_cs == IRQ_TAKEN) && !handle_irq |-> !instr_valid_i))


  // this transition exists in the RTL but unreachable. (Lastest upstream ibex removed it already)
  `ASSERT(IbexCtrlStateUnused0, ((ctrl_fsm_cs == FLUSH) |-> ctrl_fsm_ns != IRQ_TAKEN))


  `ifdef INC_ASSERT
    // If something that causes a jump into an exception handler is seen that jump must occur before
    // the next instruction executes. The logic tracks whether a jump into an exception handler is
    // expected. Assertions check the jump occurs.

    logic exception_req, exception_req_pending, exception_req_accepted, exception_req_done;
    logic exception_pc_set, seen_exception_pc_set, expect_exception_pc_set;
    logic exception_req_needs_pc_set;
    logic cs_taken_exception, ns_taken_exception;

    assign cs_taken_exception = (ctrl_fsm_cs == FLUSH);
    // || (ctrl_fsm_cs == DBG_TAKEN_IF) || (ctrl_fsm_cs == DBG_TAKEN_ID);
    assign ns_taken_exception = (ctrl_fsm_ns == FLUSH);
    // || (ctrl_fsm_ns == DBG_TAKEN_IF) || (ctrl_fsm_ns == DBG_TAKEN_ID);

    // kliu 05242024: excluding handle_irq here since handle_irq may not be processed if 
    // mstatus.mie is clearaed by the current instruction (either cssrw to mstatus or cjalr to
    // an interrupt-disabled sentry, etc)
    // assign exception_req = (special_req | enter_debug_mode | handle_irq);
    //
    // kliu 06182024: this doesn't really work with enter_debug_mode either since ctrl_fsm can 
    // go directly from FLUSH to DBG_TAKEN_IF, without going back to DECODE first. Basically the 
    // assertion logic below assumes exception requests canbe sequentialized but it's not true in
    // this case.
    // assign exception_req = (special_req | enter_debug_mode);
    assign exception_req = special_req;

    // Any exception rquest will cause a transition out of DECODE, once the controller transitions
    // back into DECODE we're done handling the request.
    // kliu 05242024: change the condition to cover the wfi case (
    // assign exception_req_done =
    // exception_req_pending & (ctrl_fsm_cs != DECODE) & (ctrl_fsm_ns == DECODE);
    assign exception_req_done =
      exception_req_pending & cs_taken_exception;

    // kliu 05242024: excluding handle_irq 
    // assign exception_req_needs_pc_set = enter_debug_mode | handle_irq | special_req_pc_change;
    assign exception_req_needs_pc_set = enter_debug_mode | special_req_pc_change;

    // An exception PC set uses specific PC types
    assign exception_pc_set =
      exception_req_pending & (pc_set_o & (pc_mux_o inside {PC_EXC, PC_ERET, PC_DRET}));

   always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        exception_req_pending   <= 1'b0;
        exception_req_accepted  <= 1'b0;
        expect_exception_pc_set <= 1'b0;
        seen_exception_pc_set   <= 1'b0;
      end else begin
        // Keep `exception_req_pending` asserted once an exception_req is seen until it is done
        exception_req_pending <= (exception_req_pending | exception_req) & ~exception_req_done;

        // The exception req has been accepted once the controller transitions out of decode
        // kliu 05242024
        //exception_req_accepted <= (exception_req_accepted & ~exception_req_done) |
        //  (exception_req & ctrl_fsm_ns != DECODE);
        exception_req_accepted <= (exception_req_accepted & ~exception_req_done) |
          (exception_req & ns_taken_exception);


        // Set `expect_exception_pc_set` if exception req needs one and keep it asserted until
        // exception req is done
        expect_exception_pc_set <= (expect_exception_pc_set | exception_req_needs_pc_set) &
          ~exception_req_done;

        // Keep `seen_exception_pc_set` asserted once an exception PC set is seen until the
        // exception req is done
        seen_exception_pc_set <= (seen_exception_pc_set | exception_pc_set) & ~exception_req_done;
      end
    end

    // Once an exception request has been accepted it must be handled before controller goes back to
    // DECODE
    `ASSERT(IbexNoDoubleExceptionReq, exception_req_accepted |-> ctrl_fsm_cs != DECODE)

    // Only signal ready, allowing a new instruction into ID, if there is no exception request
    // pending or it is done this cycle.
    `ASSERT(IbexDontSkipExceptionReq,
      id_in_ready_o |-> !exception_req_pending || exception_req_done)

    // Once a PC set has been performed for an exception request there must not be any other
    // excepting those to move into debug mode.
`ifndef FORMAL
    // the condidtion is unreachable given the new seen_exception_pc_set definition
    `ASSERT(IbexNoDoubleSpecialReqPCSet,
      seen_exception_pc_set &&
        !((ctrl_fsm_cs inside {DBG_TAKEN_IF, DBG_TAKEN_ID}) &&
          (pc_mux_o == PC_EXC) && (exc_pc_mux_o == EXC_PC_DBD))
      |-> !pc_set_o)
`endif
    // When an exception request is done there must have been an appropriate PC set (either this
    // cycle or a previous one).
    `ASSERT(IbexSetExceptionPCOnSpecialReqIfExpected,
      exception_req_pending && expect_exception_pc_set && exception_req_done |->
      seen_exception_pc_set || exception_pc_set)

    // If there's a pending exception req that doesn't need a PC set we must not see one
    `ASSERT(IbexNoPCSetOnSpecialReqIfNotExpected,
      exception_req_pending && !expect_exception_pc_set |-> ~pc_set_o)
  `endif

endmodule


////////////////////////////////////////////////////////////////
// ibex_load_store_unit
////////////////////////////////////////////////////////////////
module ibex_lsu_dv_ext import ibex_pkg::*; import cheri_pkg::*; import cheriot_dv_pkg::*; (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         lsu_req_i,
  input  logic         data_req_o,
  input  logic         lsu_addr_incr_req_o,
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
  input  logic         req_is_tbre_q,
  input  cap_rx_fsm_t  cap_rx_fsm_q,
  input  logic         data_we_q,  
  input  logic         cap_lsw_err_q,
  input  logic [32:0]  data_rdata_i,
  input  logic [32:0]  cap_lsw_q
);

  localparam MemCapFmt = load_store_unit_i.MemCapFmt;

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
    (ls_fsm_cs inside {WAIT_RVALID_MIS}) & data_req_o & lsu_addr_incr_req_o)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_1,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_GNT_MIS}) && pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_2,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE}) && data_pmp_err_i)

  logic [1:0] fcov_ls_exception_type;
  assign fcov_ls_exception_type = fcov_ls_error_exception ? 1 : fcov_ls_pmp_exception ? 2 :
                                  fcov_ls_cheri_exception ? 3 : 0;

  logic [2:0] fcov_clsc_mem_err;
  always_comb begin
    fcov_clsc_mem_err = 3'h0;       // no error;
    if ((cap_rx_fsm_q == CRX_WAIT_RESP2) && data_rvalid_i) begin
      if (data_err_i & ~data_we_q & cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h1;       // clc both word error
      else if (data_err_i & ~data_we_q & ~cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h2;       // clc word 1 error only
      else if (~data_err_i & ~data_we_q & ~cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h3;       // clc word 0 error only
      else if (data_err_i & data_we_q & cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h4;       // csc both word error
      else if (data_err_i & data_we_q & ~cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h5;       // csc word 1 error only
      else if (~data_err_i & data_we_q & cap_lsw_err_q)
         fcov_clsc_mem_err = 3'h6;       // csc word 0 error only
      else 
         fcov_clsc_mem_err = 3'h0;       // no error;
    end
  end
 
  full_cap_t   fcov_clc_mem_cap;
  logic [12:0] mem_raw_perms;
  logic [1:0]  fcov_clc_mem_cap_valid;
      
  //if (MemCapFmt) begin
    assign fcov_clc_mem_cap = mem2fullcap_fmt0_raw(data_rdata_i, cap_lsw_q);
  //end else begin
    //assign mem_raw_cap = mem2regcap_fmt1(data_rdata_i, cap_lsw_q, 4'h0);
  //end

  assign fcov_clc_mem_cap_valid  = {cap_lsw_q[32], data_rdata_i[32]};
 

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

  `ASSERT(IbexLsuFsmIdle, (((ls_fsm_cs == IDLE) && lsu_req_i)  |->
          (cap_rx_fsm_q==CRX_IDLE) | (cap_rx_fsm_q==CRX_WAIT_RESP2)))

  // `ASSERT(IbexLsuMisc1, (req_is_tbre_q == resp_is_tbre_q))
endmodule


//////////////////////////////////////////////////////////////////
// cheri_ex
////////////////////////////////////////////////////////////////

module cheri_ex_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic           cheri_exec_id_i,
  input  logic [35:0]    cheri_operator_i,
  input  logic [31:0]    pc_id_i,
  input  logic           instr_is_cheri_i,
  input  logic           instr_valid_i,
  input  logic           csr_op_en_o,
  input  logic           csr_access_o,
  input  cheri_csr_op_e  csr_op_o,
  input  logic           cheri_lsu_req,
  input  logic           is_load_cap,
  input  logic           rv32_lsu_req_i,
  input  logic [31:0]    rv32_lsu_addr_i,
  input  logic [1:0]     rv32_lsu_type_i,
  input  logic           rv32_lsu_sign_ext_i,
  input  logic           cheri_lsu_err,
  input  reg_cap_t       cheri_lsu_wcap,
  input  logic           rv32_lsu_err,
  input  logic           lsu_req_o,   
  input  logic           lsu_req_done_i,   
  input  logic           cpu_lsu_we,
  input  logic [32:0]    cpu_lsu_wdata,
  input  logic           cpu_lsu_is_cap,
  input  logic [31:0]    cpu_lsu_addr,
  input  logic           addr_incr_req_i,
  input  logic [31:0]    cs1_addr_plusimm,
  input  logic           cheri_wb_err_d
  );

  // Cheri_wb_err_d must signal retiring the current instr from ID stage and sending it to WB stage
  `ASSERT(CheriWbErrEndInstr, (cheri_wb_err_d |-> u_ibex_core.id_stage_i.instr_done));

  logic        outstanding_lsu_req;
  logic [1:0]  cpu_lsu_type;
  logic        cpu_lsu_sign_ext;
  logic [7:0]  cpu_lsu_ctrls;
  logic [31:0] cheri_lsu_start_addr;
  reg_cap_t    cpu_lsu_wcap;

  typedef enum logic [3:0] {ACC_NULL, CAP_RD, CAP_WR, BYTE_RD, BYTE_WR, 
                            HW_RD_ALIGNED, HW_RD_UNALIGNED, HW_WR_ALIGNED, HW_WR_UNALIGNED, 
                            WORD_RD_ALIGNED, WORD_RD_UNALIGNED, WORD_WR_ALIGNED, WORD_WR_UNALIGNED
                            } lsu_acc_type_e;

  lsu_acc_type_e fcov_cpu_lsu_acc;
  
  assign cpu_lsu_sign_ext = (~instr_is_cheri_i) ? rv32_lsu_sign_ext_i : 1'b0;
  assign cpu_lsu_type     = (~instr_is_cheri_i) ? rv32_lsu_type_i : 2'b00;
  assign cpu_lsu_ctrls    = {cpu_lsu_we, cpu_lsu_sign_ext, cpu_lsu_is_cap, cpu_lsu_type}; 
  assign cpu_lsu_wcap     = (instr_is_cheri_i) ? cheri_lsu_wcap : NULL_REG_CAP;

  // for rv32 accesses, addresses are formed by using ALU to do (addr_last_q +4 if addr_incr_req)
  // when addr_incr_req is owned by tbre, addr_last_q is not related with the EX instruction, there
  // the cpu_lsu_addr could be toggling when cpu_lsu_req is active. So let's just cover the cheri
  // accesses here
  assign cheri_lsu_start_addr = instr_is_cheri_i ? cs1_addr_plusimm : 0; 

  // protocol check for CPU-generated lsu requests
  // note lsu_req_o and lsu_req_done_i are for CPU request only
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      outstanding_lsu_req <= 1'b0;
    end else begin
      if (lsu_req_done_i)
        outstanding_lsu_req <= 1'b0;
      else if (lsu_req_o && ~lsu_req_done_i)
        outstanding_lsu_req <= 1'b1;
    end
  end

  // -- once asserted, req can't go low until req_done
  // -- no change in address/control signals within the same request
  `ASSERT(IbexLsuReqStable1, (lsu_req_done_i |-> lsu_req_o));
  `ASSERT(IbexLsuReqStable2, (outstanding_lsu_req |-> lsu_req_o));
  `ASSERT(IbexLsuCtrlStable, (outstanding_lsu_req |-> $stable(cpu_lsu_ctrls)));
`ifndef FORMAL
  // FV have trouble handling this since the regfile read/hazard handling is not modeled yet
  `ASSERT(IbexLsuWdataStable, ((outstanding_lsu_req & cpu_lsu_we) |-> ($stable(cpu_lsu_wdata) && $stable(cpu_lsu_wcap))));
  `ASSERT(IbexLsuAddrStable, (outstanding_lsu_req |-> $stable(cheri_lsu_start_addr)));
`endif
  // -- ensure PC/instr_execute is aligned with transactions
  // -- req & req_done is enclosed in the same instruction always
  // -- max 1 req per instruction (unless ~cheriPPLBC when CLC has to read TSMAP via LSU)
  `ASSERT(IbexLsuPCStable, (outstanding_lsu_req |-> ($stable(pc_id_i) && $stable(instr_valid_i))));

  if (u_ibex_core.CheriPPLBC) begin
    `ASSERT(IbexLsuReqEpoch, (lsu_req_done_i |-> u_ibex_core.id_stage_i.instr_done));
  end 
  
  // Cheri and RV32 LSU req can't both be active per decoder
  `ASSERT(IbexLsuReqSrc, !(cheri_lsu_req & rv32_lsu_req_i)) 

  // QQQ assertion: STKZ active won't change in the middle of load/store (thus lsu_req will stay asserted till req_done)
  // Functional coverage signals 

  `DV_FCOV_SIGNAL(logic, cpu_lsu_req, cheri_lsu_req | rv32_lsu_req_i);
  `DV_FCOV_SIGNAL(logic, cpu_lsu_err, (cheri_lsu_err | rv32_lsu_err) && (cheri_lsu_req | rv32_lsu_req_i));

  always_comb begin
    fcov_cpu_lsu_acc = ACC_NULL;
    if (cheri_lsu_req && ~cpu_lsu_we)
      fcov_cpu_lsu_acc = CAP_RD;
    else if (cheri_lsu_req)
      fcov_cpu_lsu_acc = CAP_WR;
    else if (rv32_lsu_req_i && ~cpu_lsu_we && (rv32_lsu_type_i == 2'b00) && (rv32_lsu_addr_i[1:0] == 2'b00))
      fcov_cpu_lsu_acc = WORD_RD_ALIGNED;
    else if (rv32_lsu_req_i && ~cpu_lsu_we && (rv32_lsu_type_i == 2'b00) && (rv32_lsu_addr_i[1:0] != 2'b00))
      fcov_cpu_lsu_acc = WORD_RD_UNALIGNED;
    else if (rv32_lsu_req_i && cpu_lsu_we && (rv32_lsu_type_i == 2'b00) && (rv32_lsu_addr_i[1:0] == 2'b00))
      fcov_cpu_lsu_acc = WORD_WR_ALIGNED;
    else if (rv32_lsu_req_i && cpu_lsu_we && (rv32_lsu_type_i == 2'b00) && (rv32_lsu_addr_i[1:0] != 2'b00))
      fcov_cpu_lsu_acc = WORD_WR_UNALIGNED;
    else if (rv32_lsu_req_i && ~cpu_lsu_we && (rv32_lsu_type_i == 2'b01) && (rv32_lsu_addr_i[0] == 1'b0))
      fcov_cpu_lsu_acc = HW_RD_ALIGNED;
    else if (rv32_lsu_req_i && ~cpu_lsu_we && (rv32_lsu_type_i == 2'b01) && (rv32_lsu_addr_i[0] != 1'b0))
      fcov_cpu_lsu_acc = HW_RD_UNALIGNED;
    else if (rv32_lsu_req_i && cpu_lsu_we && (rv32_lsu_type_i == 2'b01) && (rv32_lsu_addr_i[0] == 1'b0))
      fcov_cpu_lsu_acc = HW_WR_ALIGNED;
    else if (rv32_lsu_req_i && cpu_lsu_we && (rv32_lsu_type_i == 2'b01) && (rv32_lsu_addr_i[0] != 1'b0))
      fcov_cpu_lsu_acc = HW_WR_UNALIGNED;
    else if (rv32_lsu_req_i && ~cpu_lsu_we)
      fcov_cpu_lsu_acc = BYTE_RD;
    else if (rv32_lsu_req_i)
      fcov_cpu_lsu_acc = BYTE_WR;
      
  end

  logic [3:0]  fcov_ls_xfer_size;
  logic [32:0] fcov_room_in_cs1_cap;
  logic [1:0]  fcov_ls_cap_room_chk;

  always_comb begin
    if (cheri_lsu_req)
      fcov_room_in_cs1_cap = u_cheri_ex.rf_fullcap_a.top33 - u_cheri_ex.cheri_ls_chkaddr;
    else if (rv32_lsu_req_i)
      fcov_room_in_cs1_cap = u_cheri_ex.rf_fullcap_a.top33 - u_cheri_ex.rv32_ls_chkaddr + 
                             {u_cheri_ex.addr_incr_req_i, 2'b00};
    else 
      fcov_room_in_cs1_cap = 0;

    if (cheri_lsu_req)
      fcov_ls_xfer_size = 4'h8;
    else if (rv32_lsu_req_i && (rv32_lsu_type_i == 2'b00))
      fcov_ls_xfer_size = 4'h4;
    else if (rv32_lsu_req_i && (rv32_lsu_type_i == 2'b01))
      fcov_ls_xfer_size = 4'h2;
    else if (rv32_lsu_req_i)
      fcov_ls_xfer_size = 4'h1;
    else
      fcov_ls_xfer_size = 4'h0;

    fcov_ls_cap_room_chk = (fcov_room_in_cs1_cap > fcov_ls_xfer_size) ? 0 : 
                           (fcov_room_in_cs1_cap == fcov_ls_xfer_size)? 1 : 2;
  end

  `DV_FCOV_SIGNAL(logic, scr_read_only,
      (csr_op_o == CHERI_CSR_RW) && csr_access_o & ~csr_op_en_o & cheri_operator_i[CCSR_RW] & cheri_exec_id_i)
  `DV_FCOV_SIGNAL(logic, scr_write,
      (csr_op_o == CHERI_CSR_RW) && csr_op_en_o & cheri_operator_i[CCSR_RW] & cheri_exec_id_i)
 
endmodule

////////////////////////////////////////////////////////////////
// cheri_trvk_stage
////////////////////////////////////////////////////////////////

module cheri_trvk_stage_dv_ext (
  input  logic                clk_i,
  input  logic                rst_ni,
 
  input  logic                rf_trsv_en_i,
  input  logic [4:0]          rf_trsv_addr_i,
  input  logic [4:0]          rf_trvk_addr_o,
  input  logic                rf_trvk_en_o,
  input  logic                rf_trvk_clrtag_o
);
`ifndef FORMAL
  logic [4:0] tqueue[$];
  logic       trvk_err;
  int         outstanding_trsv_cnt;

  // make sure all trsv reqs will be mapped to a trvk, in order.
  initial begin 
    int i;

    tqueue = {};
    trvk_err = 1'b0;
    @(posedge rst_ni);

    while (1) begin
      @(posedge clk_i);
      if (rf_trsv_en_i) begin
        tqueue = {tqueue, rf_trsv_addr_i};
        outstanding_trsv_cnt = tqueue.size();
      end

      if (rf_trvk_en_o) begin
        trvk_err = ((tqueue.size() < 1) ||(tqueue[0] != rf_trvk_addr_o));
        tqueue   = tqueue[1:$];
        outstanding_trsv_cnt = tqueue.size();
      end
    end
  end

  `ASSERT(TrsvQueueChk, !trvk_err, clk_i, !rst_ni)
`else
  `ifdef MEM_0DLY_FORMAL
    `ASSERT(TrsvAlwaysHandled0, (rf_trsv_en_i |-> ## 4 rf_trvk_en_o ))
    `ASSERT(TrsvAlwaysHandled1, (~rf_trsv_en_i |-> ## 4 ~rf_trvk_en_o ))
    TrskAddrCorrect: assert property (@(posedge clk_i) disable iff (!rst_ni | !rf_trsv_en_i) 
      (## 4 rf_trsv_addr_i == rf_trvk_addr_o));
  `endif 
`endif
endmodule

////////////////////////////////////////////////////////////////
// cheri_tbre_wrapper
////////////////////////////////////////////////////////////////

module cheri_tbre_wrapper_dv_ext (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        tbre_lsu_req_o,
  input  logic        lsu_tbre_req_done_i,
  input  logic        lsu_tbre_sel_i,
  input  logic [1:0]  mstr_req,
  input  logic [1:0]  mstr_arbit_comb         
  );

  // protocol check for CPU-generated lsu requests
  // note lsu_req_o and lsu_req_done_i are for CPU request only
  logic        outstanding_lsu_req;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      outstanding_lsu_req <= 1'b0;
    end else begin
      if (lsu_tbre_req_done_i)
        outstanding_lsu_req <= 1'b0;
      else if (tbre_lsu_req_o && lsu_tbre_sel_i  && ~lsu_tbre_req_done_i)
        outstanding_lsu_req <= 1'b1;
    end
  end

  logic only_blk0_req;
  assign only_blk0_req = ~mstr_req[1] & mstr_req[0];

  `ASSERT(TbreWArbitOnehot, ($onehot0(mstr_arbit_comb))); 
  `ASSERT(TbreWArbitStable, (outstanding_lsu_req |-> $stable(mstr_arbit_comb))); 

  // if only blk0 req presents, always choose blk0 
  //  -- this is to ensure the arbiter doesn't lock to blk1 if blk1 req is canceled
  `ASSERT(TbreOnlyBlk0Req, (only_blk0_req |-> mstr_arbit_comb[0])); 

  // make sure we cover the blk1 req canceling corner case
  logic [1:0] mstr_arbit_comb_q;
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      mstr_arbit_comb_q <= 2'h0;
    end else begin
      mstr_arbit_comb_q <= mstr_arbit_comb;
    end
  end

  logic fcov_blk1_cancel;
  assign fcov_blk1_cancel = (mstr_arbit_comb_q == 2'b10) && only_blk0_req && ~lsu_tbre_req_done_i;

endmodule

////////////////////////////////////////////////////////////////
// cheri_tbre
////////////////////////////////////////////////////////////////

module cheri_tbre_dv_ext (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic [2:0]  req_fifo_ext_wr_ptr,
  input  logic [2:0]  cap_fifo_ext_wr_ptr,
  input  logic [2:0]  shdw_fifo_ext_wr_ptr,
  input  logic [2:0]  fifo_ext_rd_ptr,
  input  logic        tbre_lsu_req_o,
  input  logic        lsu_tbre_addr_incr_i,
  input  logic        tbre_lsu_is_cap_o,
  input  logic        tbre_lsu_we_o,
  input  logic        lsu_tbre_req_done_i,
  input  logic [31:0] tbre_lsu_addr_o,
  input  logic [32:0] tbre_lsu_wdata_o,
  input  logic        snoop_lsu_req_i,
  input  logic        snoop_lsu_req_done_i,
  input  logic        snoop_lsu_we_i,
  input  logic [31:0] snoop_lsu_addr_i,
  input  logic [31:0] load_addr,
  input  logic [31:0] store_addr
  );

  logic [2:0] req_fifo_depth, cap_fifo_depth, shdw_fifo_depth;


  assign req_fifo_depth  = req_fifo_ext_wr_ptr - fifo_ext_rd_ptr;
  assign cap_fifo_depth  = cap_fifo_ext_wr_ptr - fifo_ext_rd_ptr;
  assign shdw_fifo_depth = shdw_fifo_ext_wr_ptr - fifo_ext_rd_ptr;

  `ASSERT(TbreFIFOMaxDepth, ((req_fifo_depth<=4) && (cap_fifo_depth<=4) && (shdw_fifo_depth<=4)),
          clk_i, !rst_ni)
  `ASSERT(TbreFIFODepth, ((req_fifo_depth>=cap_fifo_depth) && (cap_fifo_depth>=shdw_fifo_depth)),
          clk_i, !rst_ni)

  `ASSERT(lsuReqDoneOneHot, $onehot0({snoop_lsu_req_done_i, lsu_tbre_req_done_i}))

  `ASSERT(tbreLsuReqDone, lsu_tbre_req_done_i |-> tbre_lsu_req_o )
  `ASSERT(snoopLsuReqDone, snoop_lsu_req_done_i |-> snoop_lsu_req_i)

  // looking for collision case
  logic fcov_tbre_fifo_hazard, fcov_tbre_fifo_head_hazard;

  initial begin
    int i;
    logic [1:0] fifo_index;

    @(posedge rst_ni);
   
    while (1) begin
      @(posedge clk_i);
      if (snoop_lsu_req_done_i) begin
        // search through req_fifo for hazard/collision case
        fcov_tbre_fifo_hazard      = 1'b0;
        fcov_tbre_fifo_head_hazard = 1'b0;
        
        for (i = 0; i < req_fifo_depth; i++) begin
          fifo_index = cheri_tbre_i.fifo_rd_ptr + i;
          if (snoop_lsu_req_done_i & snoop_lsu_we_i & cheri_tbre_i.req_fifo_mem[fifo_index][21] &&
              (snoop_lsu_addr_i[23:3] == cheri_tbre_i.req_fifo_mem[fifo_index][20:0]) &&
              (snoop_lsu_addr_i[31:24] == cheri_tbre_i.tbre_ctrl.start_addr[31:24])) begin
            fcov_tbre_fifo_hazard = 1'b1;
            if (i == 0) fcov_tbre_fifo_head_hazard = 1'b1;
          end
        end
      end else begin
        fcov_tbre_fifo_hazard      = 1'b0;
        fcov_tbre_fifo_head_hazard = 1'b0;
      end 
    end
  end

  logic [31:0] fcov_tbre_done_addr, fcov_snoop_done_addr;
  initial begin
    fcov_tbre_done_addr  = 0;
    fcov_snoop_done_addr = 0;
    @(posedge rst_ni);
   
    while (1) begin
      @(posedge clk_i);
      if (lsu_tbre_req_done_i) fcov_tbre_done_addr = tbre_lsu_addr_o;
      if (snoop_lsu_req_done_i) fcov_snoop_done_addr = snoop_lsu_addr_i;
    end

  end

  // protocol check for CPU-generated lsu requests
  // note lsu_req_o and lsu_req_done_i are for CPU request only
  logic        outstanding_lsu_req;
  logic [7:0]  tbre_lsu_ctrls;
  logic [31:0] tbre_lsu_start_addr;
  logic        lsu_cur_req_is_tbre;

  assign tbre_lsu_ctrls = {tbre_lsu_is_cap_o, tbre_lsu_we_o};  
  assign tbre_lsu_start_addr = tbre_lsu_we_o ? store_addr : load_addr;
  //assign tbre_lsu_start_addr = tbre_lsu_we_o? tbre_lsu_addr_o : 
  //                             (tbre_lsu_addr_o - {lsu_tbre_addr_incr_i, 2'b00}); 
  assign  lsu_tbre_sel = cheri_tbre_wrapper_i.lsu_tbre_sel_i & cheri_tbre_wrapper_i.mstr_arbit_comb[1];

  
  // note in the fcov_tbre_fifo_head_hazard case, TBRE may cancel a store request.
  // therefore we need lsu_cur_req_is_tbre to help make decision
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      outstanding_lsu_req <= 1'b0;
    end else begin
      if (lsu_tbre_req_done_i)
        outstanding_lsu_req <= 1'b0;
      else if (tbre_lsu_req_o && lsu_tbre_sel  && ~lsu_tbre_req_done_i)
        outstanding_lsu_req <= 1'b1;
    end
  end

  // -- once asserted, req can't go low until req_done
  // -- no change in address/control signals within the same request
  `ASSERT(TbreLsuReqStable1, (lsu_tbre_req_done_i |-> tbre_lsu_req_o));
  `ASSERT(TbreLsuCtrlStable, (outstanding_lsu_req |-> $stable(tbre_lsu_ctrls))); 
  `ASSERT(TbreLsuWdataStable, (outstanding_lsu_req & tbre_lsu_we_o |-> $stable(tbre_lsu_wdata_o))); 
  `ASSERT(TbreLsuAddrStable, (outstanding_lsu_req |-> $stable(tbre_lsu_start_addr)));

endmodule

////////////////////////////////////////////////////////////////
// cheri_stkz
////////////////////////////////////////////////////////////////

module cheri_stkz_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic          ztop_wr_i,
  input  logic [31:0]   ztop_wdata_i,
  input  full_cap_t     ztop_wfcap_i,
  input  logic          cmd_new_null,
  input  logic          cmd_new_cap,
  input  logic          cmd_cap_good,
  input  logic          lsu_stkz_req_done_i
  );

  logic [1:0] fcov_ztop_wr_type;

  always_comb begin
    if (ztop_wfcap_i.valid && (ztop_wfcap_i.base32 != ztop_wdata_i))
      fcov_ztop_wr_type = 2'h0;           
    else if  (ztop_wfcap_i.valid)
      fcov_ztop_wr_type = 2'h1;
    else if ((ztop_wfcap_i == NULL_FULL_CAP) && (ztop_wdata_i == 0))
      fcov_ztop_wr_type = 2'h2;
    else 
      fcov_ztop_wr_type = 2'h3;
  end

endmodule

////////////////////////////////////////////////////////////////
// ibex_if_stage
////////////////////////////////////////////////////////////////

module ibex_cs_registers_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic [31:0]  cheri_csr_wdata_i,
  input  reg_cap_t     cheri_csr_wcap_i,
  input  logic [31:0]  mepc_q,
  input  reg_cap_t     mepc_cap,
  input  pcc_cap_t     pcc_cap_o
  );

  full_cap_t fcov_scr_wfcap;
  full_cap_t fcov_mepc_fcap;

  assign fcov_scr_wfcap = reg2fullcap(cheri_csr_wcap_i, cheri_csr_wdata_i);
  assign fcov_mepc_fcap = reg2fullcap(mepc_cap, mepc_q);
  `ASSERT(MepcOtypeInvalid, (fcov_mepc_fcap.valid |-> (fcov_mepc_fcap.otype==0)))
  `ASSERT(MepcPermEx0, (fcov_mepc_fcap.valid |-> fcov_mepc_fcap.perms[PERM_EX]))

  `ASSERT(PccPermEx, (pcc_cap_o.valid |-> pcc_cap_o.perms[PERM_EX]))
  `ASSERT(PccOtype, (pcc_cap_o.valid |-> (pcc_cap_o.otype==0)))
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
  input  logic        instr_req_o,
  input  logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_gnt_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i,
  input  logic        rf_we_lsu,
  input  logic [35:0] cheri_operator,
  input  logic        csr_op_en,
  input  logic        instr_done_wb,
  input  logic        instr_id_done,
  input  logic        outstanding_load_wb,
  input  logic        outstanding_store_wb,
  input  logic        illegal_insn_id,
  input  logic        instr_valid_id,
  input  logic        instr_valid_clear,
  input  logic        cheri_ex_err,
  input  logic        instr_fetch_err,
  input  logic        rf_we_id,
  input  logic        cheri_csr_op_en,
  input  logic        lsu_req,
  input  logic        en_wb,
  input  logic        ready_wb,
  input  logic        ctrl_busy
  );
  // Functional coverage signals
  `DV_FCOV_SIGNAL(logic, csr_read_only,
      (u_ibex_core.csr_op == CSR_OP_READ) && u_ibex_core.csr_access && (csr_op_en || u_ibex_core.illegal_insn_id))
  `DV_FCOV_SIGNAL(logic, csr_write,
      cs_registers_i.csr_wr && u_ibex_core.csr_access && (csr_op_en || u_ibex_core.illegal_insn_id))

  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_a_id, gen_regfile_ecc.rf_ecc_err_a_id, u_ibex_core.RegFileECC)
  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_b_id, gen_regfile_ecc.rf_ecc_err_b_id, u_ibex_core.RegFileECC)

  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;

  assign outstanding_load_id  = (id_stage_i.instr_executing & (id_stage_i.lsu_req_dec & ~id_stage_i.lsu_we)) |
                                (cheri_exec_id & cheri_operator[CLOAD_CAP]);
  assign outstanding_store_id = (id_stage_i.instr_executing & id_stage_i.lsu_req_dec & id_stage_i.lsu_we) |
                                (cheri_exec_id & cheri_operator[CSTORE_CAP]);

  if (u_ibex_core.WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & load_store_unit_i.split_misaligned_access );

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

    if (u_ibex_core.WritebackStage) begin
    // cheri_ex state machines can't still  be doing an CPU LSU request when an instruction completes
    `ASSERT(CheriLsuFsmIdle1, (instr_id_done |-> 
            (load_store_unit_i.ls_fsm_ns == 0) || load_store_unit_i.cur_req_is_tbre))
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
  
  /////////////////////////////////////////////////////////
  // High-level properties to be proven by formal
  /////////////////////////////////////////////////////////
 
  // 
  // Writeback
  //
  if (u_ibex_core.WritebackStage) begin
    `ASSERT(FvxIbexWbValid, (instr_id_done |=> wb_stage_i.g_writeback_stage.wb_valid_q))
    `ifdef FORMAL
      `ASSERT(FvxIbexWbDone, (wb_stage_i.g_writeback_stage.wb_valid_q |-> ##[0:5] instr_done_wb))
    `endif
    `ASSERT(FvxIbexWbReady, (wb_stage_i.g_writeback_stage.wb_done |-> ready_wb))

    // instr_done_wb = wb_valid_q & wb_done
    logic rf_we_wb_expected;
    assign rf_we_wb_expected = instr_done_wb & 
                               (wb_stage_i.g_writeback_stage.rf_we_wb_q | 
                                wb_stage_i.g_writeback_stage.cheri_rf_we_q |
                                (wb_stage_i.g_writeback_stage.wb_instr_type_q == WB_INSTR_LOAD) |
                                wb_stage_i.g_writeback_stage.wb_cheri_load_q);

    `ASSERT(FvxIbexWbWrRegs, u_ibex_core.rf_we_wb |-> rf_we_wb_expected, clk_i, !rst_ni)
  end

  //
  // Execution
  //
  
  // Invalid/faulted instructions must not take effect
  logic instr_no_exec;
  assign instr_no_exec = ~instr_valid_id | illegal_insn_id | instr_fetch_err |
                         ~id_stage_i.controller_run | 
                         id_stage_i.controller_i.cheri_asr_err_d | id_stage_i.wb_exception;
 
  `ASSERT(FvxIbexNoExec, (id_stage_i.instr_executing |-> ~instr_no_exec))

  // No regfile write or LSU request if instruction bad or faulted
  `ASSERT(FvxIbexRfWeNoIllegal, (rf_we_id |-> id_stage_i.instr_executing))
  `ASSERT(FvxIbexLsuReqNoIllegal, (lsu_req |-> id_stage_i.instr_executing))
  `ASSERT(FvxIbexEnWbNoIllegal, (en_wb |-> id_stage_i.instr_executing))

  // No csr/scr write if instruction bad or faulted
  `ASSERT(FvxIbexCSRWeNoIllegal, (csr_op_en |-> id_stage_i.instr_executing))
  `ASSERT(FvxIbexSCRWeNoIllegal, (cheri_csr_op_en |-> id_stage_i.instr_executing))

  // Instructions are always either executed or faulted (assuming memory won't stall forever)
  // Note 
  // -- instr_id_done here includes ready_wb and instr_executing, so no exceptions
  // -- also instr_id_done and flush_id can be both true (mret and dret)
  // 
  // div instruction takes a long time to finish, so need to override it in assumptions
  // however still need to allow data memory wait states
  logic instr_terminate_id;
  assign instr_terminate_id = instr_id_done | id_stage_i.flush_id;

`ifdef FORMAL
  // in simulation div and memory access takes too long - could lead in assertion failure
  // note load/store could be delayed by TBRE arbitration & memory delay
  `ifndef MODEL_STKZ_STALL_FORMAL
    // -- use [0:15] if no STKZ stall
    `ASSERT(FvxIbexAlwaysTerminateID, (instr_valid_id |-> ##[0:15] instr_terminate_id))
    `ASSERT(FvxIbexInstrIdDone1, (id_stage_i.instr_executing |-> ##[0:15] instr_id_done))
  `else
    `ASSERT(FvxIbexAlwaysTerminateID, (instr_valid_id |-> ##[0:25] instr_terminate_id))
    // worst case -> cpu cload stalled by stkz_active, then an tbre_req (which gets in since
    // there is a 1 cycle gap betwen end of stkz stalling and cpu reclaiming memory interface
    // (since cheri_ex is using stall_q to optimize memory address timing)
    // use [0:15] if no STKZ
    `ASSERT(FvxIbexInstrIdDone1, (id_stage_i.instr_executing |-> ##[0:20] instr_id_done))
  `endif 

  `ASSERT(FvxIbexAlwaysClearID, (instr_terminate_id |-> ##[0:5] instr_valid_clear))
  `ASSERT(FvxIbexInstrDone0, (instr_id_done |-> (ready_wb & id_stage_i.instr_executing)))
`endif

  
  //
  // PC advancing & Fetching
  //

  // should keep fetching if id stage is empty, as long as the core is not sleeping
  // note IRQ handling could interrupt the fetching process and thus increase max fetch delay
`ifdef FORMAL
  // memory interface delay too long for formal
  // causes for delay here:
  //  - memory latency
  //  - NMI since it keeps interrupting the fetch process
  //  - IRQ
  //  - unaligned instructions (single memory fetch may not get a valid instruction)
  `ASSERT(FvxIbexInstrWillFetch, ((~instr_valid_id && ctrl_busy) |-> ##[0:15] if_stage_i.instr_new_id_d))
`endif

  // prove that instruction fetch data path works correctly (based on pc_if)
`ifdef FETCH_CORRECT_FORMAL  
  logic [31:0] instr_addr_q;
  logic [31:0] instr_data_assumed;
  logic [15:0] instr_lsb, instr_lsb_exp;
  logic [15:0] instr_msb, instr_msb_exp;
  logic [31:0] pc_if, pc_if_p4;
  logic        instr_lsb_good_if;
  logic        instr_msb_good_if;


  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin  
      instr_addr_q <= 32'h0;
    end else if (instr_req_o && instr_gnt_i) begin
      instr_addr_q <= instr_addr_o;
    end
  end

  assign pc_if     = if_stage_i.pc_if_o;
  assign pc_if_p4  = pc_if + 32'h4; 

  `ifdef FETCH_NO_RVC_FORMALX
    // The code below does a proof all the way to instr_out from IF stage
    // for un-compressed instructions only
    
    assign instr_data_assumed = instr_addr_q | 32'h0003_0003;
    assign instr_lsb = if_stage_i.instr_out[15:0];
    assign instr_msb = if_stage_i.instr_out[31:16];
    // assign instr_lsb_exp = pc_if[1] ? (pc_if[31:16] |16'h3) : (pc_if[15:0] |16'h3);
    assign instr_lsb_exp = pc_if[15:0]  | 16'h3;
    assign instr_msb_exp = pc_if[31:16] | 16'h3;
  `else 
    // prove to the input point of ibex_compressed decoder (still covers alignment)
    assign instr_data_assumed = instr_addr_q;
    assign instr_lsb = if_stage_i.if_instr_rdata[15:0];      // before compresed decoder
    assign instr_msb = if_stage_i.if_instr_rdata[31:16]; 
    assign instr_lsb_exp = pc_if[1] ? (pc_if[31:16]) : (pc_if[15:0]);
    assign instr_msb_exp = pc_if[1] ? (pc_if_p4[15:0]) : (pc_if[31:16]);
  `endif

  // next instructuion pushed to ID stage is considered valid
  assign instr_lsb_good_if = if_stage_i.if_id_pipe_reg_we & if_stage_i.instr_valid_id_d;
  assign instr_msb_good_if = if_stage_i.if_id_pipe_reg_we & if_stage_i.instr_valid_id_d & 
                             ~u_ibex_core.if_stage_i.instr_is_compressed;
  
  // this can only be used with the assumption specified in ibexc_if.tcl
  `ASSERT(FvxIbexFetchLsbGood, (instr_lsb_good_if |-> (instr_lsb == instr_lsb_exp )))
  `ASSERT(FvxIbexFetchMsbGood, (instr_msb_good_if |-> (instr_msb == instr_msb_exp )))
`endif

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
    {instr_err_i}, instr_rvalid_i)
//    {instr_rdata_i, instr_rdata_intg_i, instr_err_i}, instr_rvalid_i)  // we dont intialize instr memory so x is allowed for speculative fetches.

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
  
  `ASSERT_KNOWN_IF(IbexDataRPayloadX, {(data_strb & {33{~data_err_i}} &  data_rdata_i), 
    ({7{~u_ibex_core.load_store_unit_i.data_we_q}} & data_rdata_intg_i), data_err_i}, data_rvalid_i)

  `ASSERT_KNOWN(IbexIrqX, {irq_software_i, irq_timer_i, irq_external_i, irq_fast_i, irq_nm_i})

  `ASSERT_KNOWN(IbexScrambleKeyValidX, u_ibex_top.scramble_key_valid_i)
  `ASSERT_KNOWN_IF(IbexScramblePayloadX, {u_ibex_top.scramble_key_i, u_ibex_top.scramble_nonce_i}, u_ibex_top.scramble_key_valid_i)

  `ASSERT_KNOWN(IbexDebugReqX, debug_req_i)
  `ASSERT_KNOWN(IbexFetchEnableX, fetch_enable_i)

  //////////////////////////////////////////////////////////
  // Assumptions defined for formal verification
  //////////////////////////////////////////////////////////
`ifdef FORMAL
  //
  // Constant tie-offs
  //
  AssumeCfgCheriMode:   assume property (cheri_pmode_i == 1'b1);
  AssumeCfgTsafe:       assume property (cheri_tsafe_en_i == 1'b1);
  AssumeCfgNotTestMode: assume property (test_en_i == 1'b0);
  AssumeCfgBootAddr:    assume property (boot_addr_i == 32'h8000_0000);

  AssumeFetchEnable: assume property (fetch_enable_i == 1'b1);

  //
  // NMI/debug I/O, etc.
  //
  // NMI causes WillFetch to fail since it keeps interrupting the fetch process
  AssumeNoNMI:  assume property (irq_nm_i == 1'b0);    

  // for controller assertion IbexSetExceptionPCOnSpecialReqIfExpected
  // enter_debug_mode is not covered by assertion logic right now. QQQ
  AssumeNoDebug: assume property (debug_req_i == 1'b0);

  //
  // Memory interface I/O assumptions
  //
  logic data_rvalid_exp, instr_rvalid_exp;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      data_rvalid_exp  <= 1'b0;
      instr_rvalid_exp <= 1'b0;
    end else begin
      data_rvalid_exp  <= data_req_o & data_gnt_i;
      instr_rvalid_exp <= instr_req_o & instr_gnt_i;
    end
  end

  // model the data/instruction interface (gnt/rvalid always comes back after req)
  `ifdef MEM_0DLY_FORMAL
    AssumeDataGntNoDly0:   assume property (data_req_o |-> data_gnt_i);
    AssumeDataGntNoDly1:   assume property (~data_req_o |-> ~data_gnt_i);
    //AssumeDataValidNoDly0: assume property (data_req_o |=> data_rvalid_i);
    //AssumeDataValidNoDly1: assume property (~data_req_o |=> ~data_rvalid_i);
    AssumeDataValid: assume property (data_rvalid_i == data_rvalid_exp);

    AssumeInstrGntNoDly0:   assume property (instr_req_o |-> instr_gnt_i);
    AssumeInstrGntNoDly1:   assume property (~instr_req_o |-> ~instr_gnt_i);
    // AssumeInstrValidNoDly0: assume property (instr_req_o |=> instr_rvalid_i);
    // AssumeInstrValidNoDly1: assume property (~instr_req_o |=> ~instr_rvalid_i);
    AssumeInstrValid: assume property (instr_rvalid_i == instr_rvalid_exp);
  `else 
    // assume data_gnt can happen any time, don't constrain it.
    // also note, ##2 also proves but run time is longer
    AssumeDataGnt0:  assume property (data_req_o |-> ##[0:2] data_gnt_i);
    AssumeDataGnt1:  assume property ((~rst_ni|~data_req_o) |-> ~data_gnt_i);
    AssumeDataValid: assume property (data_rvalid_i == data_rvalid_exp);
    //AssumeDataIntf3: assume property (##1 data_rvalid_i == ~rst_ni & $past (data_req_o & data_gnt_i));
    //AssumeDataIntf4: assume property (~rst_ni |-> ~data_rvalid_i);
    
    //`ASSERT(x1, (data_rvalid_i == data_rvalid_exp))

    AssumeInstrGnt0: assume property (instr_req_o |-> ##[0:3] instr_gnt_i);
    AssumeInstrGnt1: assume property ((~rst_ni | ~instr_req_o) |-> ~instr_gnt_i);
    AssumeInstrValid: assume property (instr_rvalid_i == instr_rvalid_exp);
    //AssumeInstrValid0: assume property ((instr_req_o & instr_gnt_i) |=> instr_rvalid_i);
    //AssumeInstrValid1: assume property (~(instr_req_o & instr_gnt_i) |=> ~instr_rvalid_i);
  `endif 

  `ifdef FETCH_CORRECT_FORMAL  
    AssumeFetchedInstr: assume property (instr_rdata_i == u_ibex_core.ibex_core_dv_ext_i.instr_data_assumed);
  `endif
 
  //
  // Model tbre mmreg i/o interface
  //
  AssumeMMreg0: assume property ($stable(u_ibex_core.cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_ctrl.start_addr));
  AssumeMmreg1: assume property ($stable(u_ibex_core.cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_ctrl.end_addr));
  AssumeMmreg2: assume property ($stable(u_ibex_core.cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_ctrl.add1wait));

  //
  // Internal signal assumptions
  //

  `ifndef MODEL_STKZ_STALL_FORMAL
    AssumeStkzStall0: assume property (u_ibex_core.g_cheri_ex.u_cheri_ex.cpu_stall_by_stkz_o == 1'b0);
    AssumeStkzStall1: assume property (u_ibex_core.g_cheri_ex.u_cheri_ex.cpu_grant_to_stkz_o == 1'b0);
  `else
    `ifdef FAST_STKZ_FORMAL
      AssumeStkzFast0: assume property (u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.ztop_wdata_i <= u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.ztop_wfcap_i.base32 + 4);
      AssumeStkzData1: assume property (u_ibex_core.cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.ztop_wfcap_i.base32 < 32'hfff_fffc);
    `endif
  `endif

  // div instruction takes too long for the tool to converge 
  // jasperGold complains about precondition unreachable for this, however without this assumption IbexInstrAlwaysRetireID won't prove
  AssumeFastDiv: assume property (disable iff (~rst_ni) u_ibex_core.ex_block_i.gen_multdiv_fast.multdiv_i.div_en_i |-> u_ibex_core.ex_block_i.gen_multdiv_fast.multdiv_i.valid_o);


`endif

endmodule
