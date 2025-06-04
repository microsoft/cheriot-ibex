// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define TOP_PATH kudu_top
`define ISSUER_PATH kudu_top.issuer_i
`define COMMITTER_PATH kudu_top.committer_i

module tracer_wrapper import super_pkg::*; import tracer_pkg::*; import cheri_pkg::*; (
  input logic        clk_i,
  input logic        rst_ni,
  input logic        cheri_pmode_i
);

  typedef struct packed {
    logic [4:0]  pl;
    logic        is_ex;   // instr actually goes to commit FIFO and EX pipelines
    rvfi_t       rvfi;
    ir_dec_t     ir_dec;
  } instr_trace_t;
  
  function automatic logic [31:0] get_pc_wdata (int ir_sel);
    logic [31:0] result;
    // only need to conside issued branch/jal/jalr instructions (rvfi.valid == 1)
    // note this is basically 
    ir_dec_t      ir_dec;
    logic         mis_taken, mis_not_taken;
    logic         branch_taken;
    logic         any_err;

    if (ir_sel == 0) begin
      ir_dec        = `ISSUER_PATH.ir0_dec;
      mis_taken     = `ISSUER_PATH.branch_info_i.mispredict_taken[0];
      mis_not_taken = `ISSUER_PATH.branch_info_i.mispredict_not_taken[0];
      branch_taken  = `ISSUER_PATH.branch_info_i.branch_taken[0];
      any_err       = `ISSUER_PATH.ir_any_err[0];
    end else begin
      ir_dec        = `ISSUER_PATH.ir1_dec;
      mis_taken     = `ISSUER_PATH.branch_info_i.mispredict_taken[1];
      mis_not_taken = `ISSUER_PATH.branch_info_i.mispredict_not_taken[1];
      branch_taken  = `ISSUER_PATH.branch_info_i.branch_taken[1];
      any_err       = `ISSUER_PATH.ir_any_err[1];
    end

    if (any_err) 
      result = ir_dec.pc_nxt;  // somehow this is the ibex tracer behavor - should use the instr.btarget?
    else if (ir_dec.is_jalr) 
      result = `TOP_PATH.ex_pc_target; 
    else if ((ir_dec.is_jal | ir_dec.is_branch) & branch_taken & mis_taken)
      result = `TOP_PATH.ex_pc_target; 
    else if ((ir_dec.is_jal | ir_dec.is_branch) & branch_taken)
      result = ir_dec.ptarget;
    else
      result = ir_dec.pc_nxt;
     
    return result;    
  endfunction

  function automatic instr_trace_t get_trace_issued (int ir_sel);
    instr_trace_t  result; 
    logic [31:0]   insn32;
    opcode_e       opcode;

    op_data2_t ir0_op_data2_fwd, ir1_op_data2_fwd;

    ir0_op_data2_fwd = `ISSUER_PATH.ira_is0_i ? `ISSUER_PATH.ira_op_data2_fwd : `ISSUER_PATH.irb_op_data2_fwd; 
    ir1_op_data2_fwd = `ISSUER_PATH.ira_is0_i ? `ISSUER_PATH.irb_op_data2_fwd : `ISSUER_PATH.ira_op_data2_fwd; 

    result.rvfi.order  = 0;     // QQQ not used for now
    result.rvfi.halt   = 1'b0;
    result.rvfi.intr   = 1'b0;
    result.rvfi.mode   = 1'b0;
    result.rvfi.ixl    = 1'b0;

    if (ir_sel == 0) begin    // IR0
      insn32                 = `ISSUER_PATH.ir0_dec.insn;
      result.pl              = `ISSUER_PATH.ir0_pl_sel;
      result.ir_dec          = `ISSUER_PATH.ir0_dec;
      result.is_ex           = (| `ISSUER_PATH.ir0_pl_sel[4:1]);
      result.rvfi.valid      = `ISSUER_PATH.ir0_issued | `ISSUER_PATH.ir0_trap_event;     
      result.rvfi.insn       = `ISSUER_PATH.ir0_dec.is_comp ?  `ISSUER_PATH.ir0_dec.c_insn : `ISSUER_PATH.ir0_dec.insn;
      result.rvfi.trap       = `ISSUER_PATH.ir0_trap_event;
      result.rvfi.rs1_addr   = `ISSUER_PATH.ir0_dec.rs1;
      result.rvfi.rs2_addr   = `ISSUER_PATH.ir0_dec.rs2;
      result.rvfi.rs3_addr   = 0;
      result.rvfi.rs1_rdata  = ir0_op_data2_fwd.d0;
      result.rvfi.rs2_rdata  = ir0_op_data2_fwd.d1;
      result.rvfi.rs3_rdata  = 0;
      result.rvfi.pc_rdata   = `ISSUER_PATH.ir0_dec.pc;
      result.rvfi.pc_wdata   = get_pc_wdata(0);
    end else begin            // IR1
      insn32                 = `ISSUER_PATH.ir1_dec.insn;
      result.pl              = `ISSUER_PATH.ir1_pl_sel;
      result.ir_dec          = `ISSUER_PATH.ir1_dec;
      result.is_ex           = (| `ISSUER_PATH.ir1_pl_sel[4:1]);
      result.rvfi.valid      = `ISSUER_PATH.ir1_issued;     
      result.rvfi.insn       = `ISSUER_PATH.ir1_dec.is_comp ?  `ISSUER_PATH.ir1_dec.c_insn : `ISSUER_PATH.ir1_dec.insn;
      result.rvfi.trap       = 1'b0;    // trap can only happen on IR0
      result.rvfi.rs1_addr   = `ISSUER_PATH.ir1_dec.rs1;
      result.rvfi.rs2_addr   = `ISSUER_PATH.ir1_dec.rs2;
      result.rvfi.rs3_addr   = 0;
      result.rvfi.rs1_rdata  = ir1_op_data2_fwd.d0;
      result.rvfi.rs2_rdata  = ir1_op_data2_fwd.d1;
      result.rvfi.rs3_rdata  = 0;
      result.rvfi.pc_rdata   = `ISSUER_PATH.ir1_dec.pc;
      result.rvfi.pc_wdata   = get_pc_wdata(1);
    end

    opcode                 = opcode_e'(insn32[6:0]);

    result.rvfi.mem_rmask = 0;
    result.rvfi.mem_wmask = 0;

    if (opcode == OPCODE_LOAD) begin
      if (insn32[13:12] == 2'b00) 
        result.rvfi.mem_rmask = 4'b0001;        // byte
      else if  (insn32[13:12] == 2'b01)
        result.rvfi.mem_rmask = 4'b0011;        // half word 
      else
        result.rvfi.mem_rmask = 4'b1111;        // word 
    end else if (opcode == OPCODE_STORE) begin   
      if (insn32[13:12] == 2'b00) 
        result.rvfi.mem_wmask = 4'b0001;        // byte
      else if  (insn32[13:12] == 2'b01)
        result.rvfi.mem_wmask = 4'b0011;        // half word 
      else
        result.rvfi.mem_wmask = 4'b1111;        // word 
    end        

    // fill later at the committer side
    result.rvfi.rd_addr    = 0;
    result.rvfi.rd_wdata   = 0;
    result.rvfi.mem_addr   = 0;
    result.rvfi.mem_wdata  = 0;
    result.rvfi.mem_rdata  = 0;
    result.rvfi.mem_is_cap = 1'b0;

    return result;
  endfunction

  logic         rvfi_req;
  rvfi_t        rvfi_data;
  instr_trace_t instr_trace_fifo[$];


  tracer tracer_i (
    .clk_i         (clk_i         ),
    .rst_ni        (rst_ni        ),
    .cheri_pmode_i (cheri_pmode_i ),
    .hart_id_i     (32'h0         ),
    .rvfi_req_i    (rvfi_req      ),
    .rvfi_data_i   (rvfi_data     )
  );

  // case 0: normal ex/commit
  // case 1: branch. ir_rdy, don't go to ex/commit.
  // case 2: jal. ir_rdy, set pc, also go to ex/commit
  // case 3: issue side error (illegal, fetch errs). no ir_rdy. directly flush IF
  rvfi_t rvfi_req_queue[$];
  
  logic [1:0]      cmt_good;
  logic            cmt_flush;
  instr_trace_t    instr_a, instr_b;
  logic [4:0]      cmt_pl0, cmt_pl1;
  logic [31:0]     cmt_pc0, cmt_pc1;
  logic            is_load;
  logic [31:0]     mem_addr;
  logic            irq_issued;
  logic [MemW-1:0] mem_wdata;
  logic [RegW-1:0] mem_rdata;
  logic [2:0]      rf_we_vec;

  assign cmt_pl0     = `TOP_PATH.sbdfifo_rdata0.pl;
  assign cmt_pl1     = `TOP_PATH.sbdfifo_rdata1.pl;
  assign cmt_pc0     = `TOP_PATH.sbdfifo_rdata0.pc;
  assign cmt_pc1     = `TOP_PATH.sbdfifo_rdata1.pc;

  // note in committer if instr0 is erred we still dequeue instr1 from SBD fifo but won't write regfile
  assign cmt_good[0] = `TOP_PATH.sbdfifo_rd_valid[0] & `TOP_PATH.sbdfifo_rd_rdy[0];
  assign cmt_good[1] = `TOP_PATH.sbdfifo_rd_valid[1] & `TOP_PATH.sbdfifo_rd_rdy[1] & ~`COMMITTER_PATH.instr_err[0];

  assign cmt_flush   = `TOP_PATH.cmt_flush;
  assign irq_issued  = (`ISSUER_PATH.ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) && (`ISSUER_PATH.special_case_q == IRQ) ;
  assign is_load     = `TOP_PATH.lspl_output.we;
  assign mem_addr    = `TOP_PATH.ls_pipeline_i.rvfi_mem_addr;
  assign mem_wdata   = is_load ? 0 : `TOP_PATH.ls_pipeline_i.rvfi_mem_wdata;
  assign mem_rdata   = is_load ? `TOP_PATH.lspl_output.wdata : 0;
  assign rf_we_vec   = {`COMMITTER_PATH.rf_we2_o, `COMMITTER_PATH.rf_we1_o, `COMMITTER_PATH.rf_we0_o};

  initial begin
    int         i;
    int         ex_pop_cnt, cmt_cnt;
    logic       irq_status;
    logic       rf_we;

    instr_trace_fifo = {};
    rvfi_req         = 1'b0;
    irq_status       = 1'b0;

    @(posedge rst_ni);
    
    while (1) begin
      @(posedge clk_i);    // note we work at time 0 after posedge clk, before flops updated

      // push fifo entry at issue side
      for (i = 0; i < 2; i++) begin
        instr_a = get_trace_issued(i);
        if (instr_a.rvfi.valid) begin 
          instr_a.rvfi.intr = irq_status;
          instr_trace_fifo = {instr_trace_fifo, instr_a};
          // $display("instr_a: pc = %x, pl = %x", instr_a.rvfi.pc_rdata, instr_a.pl);
          irq_status = 1'b0;
        end
      end
      
      if (irq_issued) irq_status = 1'b1;

      // pop fifo entry at commmit side
      cmt_cnt = 0;
      if (cmt_good[0]) cmt_cnt++;
      if (cmt_good[1]) cmt_cnt++;
      // $display("time = %t, cmt_cnt = %d", $time, cmt_cnt);

      ex_pop_cnt = 0;
      rvfi_req_queue = {};

      if (cmt_flush) instr_trace_fifo = {};    

      while (instr_trace_fifo.size() > 0) begin
        instr_b = instr_trace_fifo[0];

        // keep popping from the fifo till the next uncommmited EX entry
        // - so we are reading a least cmt_cnt EX entries, and whatever non-EX entries before that
        if (instr_b.is_ex &&  (ex_pop_cnt >= cmt_cnt)) begin
          break;
        end else begin
          // $display("--- instr_b.pc = %x, pl = %x", instr_b.rvfi.pc_rdata, instr_b.pl);

          if (instr_b.is_ex) begin 
            if (instr_b.is_ex && (ex_pop_cnt == 0) && (cmt_pl0 != instr_b.pl)) 
              $error("--- Error!!! EX commit %d not matching: %x, %x, %x, %x", ex_pop_cnt, cmt_pl0, 
                     instr_b.pl, cmt_pc0, instr_b.ir_dec.pc);
            else if (instr_b.is_ex && (ex_pop_cnt == 1) && (cmt_pl1 != instr_b.pl))
              $error("--- Error!!! EX commit %d not matching: %x, %x, %x, %x", ex_pop_cnt, cmt_pl1, 
                     instr_b.pl, cmt_pc1, instr_b.ir_dec.pc);

            // figure out the rf_we status for instr_b
            // RVFI requires to set rd_addr to 0 if rf_we is deasserted (trap, etc)
            rf_we = instr_b.pl[3] ? rf_we_vec[2] : 
                                   ((ex_pop_cnt == 0) ? rf_we_vec[0] : rf_we_vec[1]);

            // fill EX instruction info using pipeline outputs
            if (instr_b.pl[1]) begin
              instr_b.rvfi.rd_addr    = rf_we ? `TOP_PATH.alupl0_output.waddr : 0;
              instr_b.rvfi.rd_wdata   = `TOP_PATH.alupl0_output.wdata;
              instr_b.rvfi.trap       = instr_b.rvfi.trap | `TOP_PATH.alupl0_output.err;
            end else if (instr_b.pl[2]) begin
              instr_b.rvfi.rd_addr    = rf_we ? `TOP_PATH.alupl1_output.waddr : 0;
              instr_b.rvfi.rd_wdata   = `TOP_PATH.alupl1_output.wdata;
              instr_b.rvfi.trap       = instr_b.rvfi.trap | `TOP_PATH.alupl1_output.err;
            end else if (instr_b.pl[3]) begin
              instr_b.rvfi.rd_addr    = rf_we ? `TOP_PATH.lspl_output.waddr : 0;
              instr_b.rvfi.rd_wdata   = is_load ? mem_rdata : 0;
              instr_b.rvfi.mem_addr   = mem_addr;
              instr_b.rvfi.mem_wdata  = mem_wdata;
              instr_b.rvfi.mem_rdata  = mem_rdata;
              instr_b.rvfi.trap       = instr_b.rvfi.trap | `TOP_PATH.lspl_output.err;
            end else if (instr_b.pl[4]) begin
              instr_b.rvfi.rd_addr    = rf_we ? `TOP_PATH.multpl_output.waddr : 0;
              instr_b.rvfi.rd_wdata   = `TOP_PATH.multpl_output.wdata;
              instr_b.rvfi.trap       = instr_b.rvfi.trap | `TOP_PATH.multpl_output.err;
            end

            ex_pop_cnt ++;
          end

          // match ibex RVFI implementation
          if (instr_b.rvfi.rd_addr == 0) instr_b.rvfi.rd_wdata = 0;
          if (instr_b.rvfi.rd_addr == 0) instr_b.rvfi.mem_rdata = 0; 
          if (instr_b.rvfi.trap) instr_b.rvfi.mem_rmask = 0;
          if (instr_b.rvfi.trap) instr_b.rvfi.mem_wmask = 0;

          // send req to tracer and pop it from fifo
          rvfi_req_queue = {rvfi_req_queue, instr_b.rvfi};

          instr_trace_fifo =  instr_trace_fifo[1:$];
        end
      end  // while (pop)
      
      // send req to tracer in one shot, simulation time advanced
      while (rvfi_req_queue.size() > 0) begin
          rvfi_data = rvfi_req_queue[0];
          #0.5; rvfi_req  = 1'b1;
          #0.5; rvfi_req  = 1'b0;
          rvfi_req_queue = rvfi_req_queue[1:$];
      end
    end
  end

endmodule
