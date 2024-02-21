// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
  bind ibex_core             ibex_core_dv_ext          ibex_core_dv_ext_i (.*);
  bind ibex_top              ibex_top_dv_ext           ibex_top_dv_ext_i (.*);
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
// ibex_id_stage
////////////////////////////////////////////////////////////////

module ibex_id_stage_dv_ext (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic [31:0] rf_reg_rdy_i,
  input  logic        rf_ren_a,
  input  logic [4:0]  rf_raddr_a_o,
  input  logic        rf_ren_b,
  input  logic [4:0]  rf_raddr_b_o,
  input  logic        cheri_rf_we,
  input  logic [4:0]  rf_waddr_id_o,
  input  logic        cheri_exec_id_o,
  input  logic        instr_executing
);

  logic [2:0] fcov_trvk_stall_cause;

  assign fcov_trvk_stall_cause[0] = rf_ren_a && ~rf_reg_rdy_i[rf_raddr_a_o];
  assign fcov_trvk_stall_cause[1] = rf_ren_b && ~rf_reg_rdy_i[rf_raddr_b_o];
  assign fcov_trvk_stall_cause[2] = cheri_rf_we && ~rf_reg_rdy_i[rf_waddr_id_o]; 

  `ASSERT(IbexExecInclCheri, (cheri_exec_id_o |-> instr_executing))
 


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
  input  pc_sel_e               pc_mux_o
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

   always @(posedge clk_i, negedge rst_ni) begin
     if (~rst_ni) begin
       cpu_in_isr <= 1'b0;
     end else begin 
       if (((ctrl_fsm_cs == FLUSH) && pc_set_o && (pc_mux_o == PC_EXC)) ||
           (ctrl_fsm_cs == IRQ_TAKEN))
         cpu_in_isr <= 1'b1;
       else if ((ctrl_fsm_cs == FLUSH) && pc_set_o && (pc_mux_o == PC_ERET))
         cpu_in_isr <= 1'b0;
     end

   end



endmodule


////////////////////////////////////////////////////////////////
// ibex_load_store_unit
////////////////////////////////////////////////////////////////
module ibex_lsu_dv_ext import ibex_pkg::*; import cheri_pkg::*; (
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
  input  logic         resp_is_tbre_q,
  input  cap_rx_fsm_t  cap_rx_fsm_q,
  input  logic         data_we_q,  
  input  logic         cap_lsw_err_q  

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
  input  logic           addr_incr_req_i
  );

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
  // the address will be toggling when cpu_lsu_req is active.
  assign cheri_lsu_start_addr = instr_is_cheri_i ? (cpu_lsu_addr - {addr_incr_req_i, 2'b00}) : 0; 

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
  `ASSERT(IbexLsuWdataStable, ((outstanding_lsu_req & cpu_lsu_we) |-> ($stable(cpu_lsu_wdata) && $stable(cpu_lsu_wcap))));
  `ASSERT(IbexLsuAddrStable, (outstanding_lsu_req |-> $stable(cheri_lsu_start_addr)));
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
  input  logic [31:0] snoop_lsu_addr_i
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
  assign tbre_lsu_start_addr = tbre_lsu_we_o? tbre_lsu_addr_o : 
                               (tbre_lsu_addr_o - {lsu_tbre_addr_incr_i, 2'b00}); 
  assign  lsu_tbre_sel = cheri_tbre_wrapper_i.lsu_tbre_sel_i;

  
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
  `ASSERT(TbreLsuReqStable2, (outstanding_lsu_req |-> tbre_lsu_req_o));
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
  input  logic          cmd_new,
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

endmodule
