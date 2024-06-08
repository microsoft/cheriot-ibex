// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`include "core_ibex_csr_categories.svh"

interface core_ibex_fcov_if import ibex_pkg::*; import cheri_pkg::*; (
  input clk_i,
  input rst_ni,

  input priv_lvl_e priv_mode_id,
  input priv_lvl_e priv_mode_lsu,

  input debug_mode,

//  input fcov_rf_ecc_err_a_id,
//  input fcov_rf_ecc_err_b_id,

  input fetch_enable_t fetch_enable_i
);
  `include "dv_fcov_macros.svh"
  //import uvm_pkg::*;

  typedef enum {
    InstrCategoryALU,
    InstrCategoryMul,
    InstrCategoryDiv,
    InstrCategoryBranch,
    InstrCategoryCJAL,
    InstrCategoryCJALR,
    InstrCategoryLoad,
    InstrCategoryStore,
    InstrCategoryCSRAccess,
    InstrCategoryEBreakDbg,
    InstrCategoryEBreakExc,
    InstrCategoryECall,
    InstrCategoryMRet,
    InstrCategoryDRet,
    InstrCategoryWFI,
    InstrCategoryFence,
    InstrCategoryFenceI,
    InstrCategoryCheriQuery,           // cs1 --> rd
    InstrCategoryCheriMod,             // cs1, rs2|cs2 --> cd
    InstrCategoryCheriAddr,            // cs1, [rs2] --> cd
    InstrCategoryCheriBounds,          // cs1, [rs2] --> cd
    InstrCategoryCheriCLC,
    InstrCategoryCheriCSC,
    InstrCategoryCheriSCR,
    InstrCategoryNone,
    InstrCategoryFetchError,
    InstrCategoryCompressedIllegal,
    InstrCategoryUncompressedIllegal,
    InstrCategoryCSRIllegal,
    InstrCategoryPrivIllegal,
    InstrCategoryOtherIllegal,
    // Category not in coverage plan, it should never be seen. An instruction given the Other
    // category should either be classified under an existing category or a new category should be
    // created as appropriate.
    InstrCategoryOther
  } instr_category_e;

  typedef enum {
    IdStallTypeNone,
    IdStallTypeInstr,
    IdStallTypeLdHz,
    IdStallTypeMem,
    IdStallTypeTRVK
  } id_stall_type_e;

  instr_category_e id_instr_category, wb_instr_category, id_instr_category_q;

  // Set `id_instr_category` to the appropriate category for the uncompressed instruction in the
  // ID/EX stage.  Compressed instructions are not handled (`id_stage_i.instr_rdata_i` is always
  // uncompressed).  When the `id_stage.instr_valid_i` isn't set `InstrCategoryNone` is the given
  // instruction category.
  logic [35:0] cheri_ops;
  assign   cheri_ops = id_stage_i.cheri_operator_o;
  cheri_op_e fcov_cheri_instr;

  always_comb begin
    int i;
    for (i=0;i<32;i++) 
      if ((cheri_ops >> i) & 1) fcov_cheri_instr = cheri_op_e'(i);
  end

  always_comb begin

    id_instr_category = InstrCategoryOther;

    case (id_stage_i.instr_rdata_i[6:0])
      ibex_pkg::OPCODE_LUI:    id_instr_category = InstrCategoryALU;
      // ibex_pkg::OPCODE_AUIPC:  id_instr_category = InstrCategoryALU;
      ibex_pkg::OPCODE_JAL:    id_instr_category = InstrCategoryCJAL;
      ibex_pkg::OPCODE_JALR:   id_instr_category = InstrCategoryCJALR;
      ibex_pkg::OPCODE_BRANCH: id_instr_category = InstrCategoryBranch;
      ibex_pkg::OPCODE_LOAD:   id_instr_category = InstrCategoryLoad;
      ibex_pkg::OPCODE_STORE:  id_instr_category = InstrCategoryStore;
      ibex_pkg::OPCODE_OP_IMM: id_instr_category = InstrCategoryALU;
      ibex_pkg::OPCODE_OP: begin
        if ({id_stage_i.instr_rdata_i[26], id_stage_i.instr_rdata_i[13:12]} == {1'b1, 2'b01}) begin
          id_instr_category = InstrCategoryALU; // reg-reg/reg-imm ops
        end else if (id_stage_i.instr_rdata_i[31:25] inside {7'b000_0000, 7'b010_0000, 7'b011_0000,
              7'b011_0100, 7'b001_0100, 7'b001_0000, 7'b000_0101, 7'b000_0100, 7'b010_0100}) begin
          id_instr_category = InstrCategoryALU; // RV32I and RV32B reg-reg/reg-imm ops
        end else if (id_stage_i.instr_rdata_i[31:25] == 7'b000_0001) begin
          if (id_stage_i.instr_rdata_i[14]) begin
            id_instr_category = InstrCategoryDiv; // DIV*
          end else begin
            id_instr_category = InstrCategoryMul; // MUL*
          end
        end
      end
      ibex_pkg::OPCODE_SYSTEM: begin
        if (id_stage_i.instr_rdata_i[14:12] == 3'b000) begin
          case (id_stage_i.instr_rdata_i[31:20])
            12'h000: id_instr_category = InstrCategoryECall;
            12'h001: begin
              if (id_stage_i.debug_ebreakm_i && priv_mode_id == PRIV_LVL_M) begin
                id_instr_category = InstrCategoryEBreakDbg;
              end else if (id_stage_i.debug_ebreaku_i && priv_mode_id == PRIV_LVL_U) begin
                id_instr_category = InstrCategoryEBreakDbg;
              end else begin
                id_instr_category = InstrCategoryEBreakExc;
              end
            end
            12'h302: id_instr_category = InstrCategoryMRet;
            12'h7b2: id_instr_category = InstrCategoryDRet;
            12'h105: id_instr_category = InstrCategoryWFI;
          endcase
        end else begin
          id_instr_category = InstrCategoryCSRAccess;
        end
      end
      ibex_pkg::OPCODE_MISC_MEM: begin
        case (id_stage_i.instr_rdata_i[14:12])
          3'b000: id_instr_category = InstrCategoryFence;
          3'b001: id_instr_category = InstrCategoryFenceI;
        endcase
      end
      default: id_instr_category = InstrCategoryOther;
    endcase

    // CHERI decoding takes precedance
    case(1'b1)
      cheri_ops[CCSR_RW]:
        id_instr_category = InstrCategoryCheriSCR;
      cheri_ops[CSET_ADDR], cheri_ops[CINC_ADDR], cheri_ops[CINC_ADDR_IMM], cheri_ops[CAUICGP],cheri_ops[CAUIPCC]:
        id_instr_category = InstrCategoryCheriAddr;
      cheri_ops[CSET_BOUNDS_IMM], cheri_ops[CSET_BOUNDS], cheri_ops[CSET_BOUNDS_EX], cheri_ops[CRRL], cheri_ops[CRAM]:
        id_instr_category = InstrCategoryCheriBounds;
      cheri_ops[CCLEAR_TAG], cheri_ops[CMOVE_CAP], cheri_ops[CSEAL], cheri_ops[CUNSEAL], cheri_ops[CAND_PERM],
      cheri_ops[CSUB_CAP], cheri_ops[CIS_SUBSET], cheri_ops[CIS_EQUAL], cheri_ops[CSET_HIGH]:
        id_instr_category = InstrCategoryCheriMod;
      cheri_ops[CGET_PERM], cheri_ops[CGET_TYPE], cheri_ops[CGET_BASE], cheri_ops[CGET_TOP], 
      cheri_ops[CGET_LEN], cheri_ops[CGET_TAG], cheri_ops[CGET_ADDR], cheri_ops[CGET_HIGH]: 
        id_instr_category = InstrCategoryCheriQuery;
      cheri_ops[CLOAD_CAP]:
        id_instr_category = InstrCategoryCheriCLC;
      cheri_ops[CSTORE_CAP]:
        id_instr_category = InstrCategoryCheriCSC;
    endcase

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.instr_fetch_err_i) begin
        id_instr_category = InstrCategoryFetchError;
      end else if (id_stage_i.illegal_c_insn_i) begin
        id_instr_category = InstrCategoryCompressedIllegal;
      end else if (id_stage_i.illegal_insn_dec) begin
        id_instr_category = InstrCategoryUncompressedIllegal;
      end else if (id_stage_i.illegal_csr_insn_i) begin
//        if (cs_registers_i.illegal_csr_priv || cs_registers_i.illegal_csr_dbg) begin
        if (cs_registers_i.illegal_csr_priv) begin
          id_instr_category = InstrCategoryPrivIllegal;
        end else begin
          id_instr_category = InstrCategoryCSRIllegal;
        end
      end else if (id_stage_i.illegal_insn_o) begin
//        if (id_stage_i.illegal_dret_insn || id_stage_i.illegal_umode_insn) begin
//          id_instr_category = InstrCategoryPrivIllegal;
//        end else begin
          id_instr_category = InstrCategoryOtherIllegal;
//        end
      end
    end else begin
      id_instr_category = InstrCategoryNone;
    end
  end

  logic [1:0] fcov_id_exc_int, fcov_id_exc_int_q;

  assign fcov_id_exc_int = {id_stage_i.controller_i.handle_irq, id_stage_i.controller_i.special_req_pc_change};

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wb_instr_category   <= InstrCategoryNone;
      id_instr_category_q <= InstrCategoryNone;
      fcov_id_exc_int_q   <= 0;
    end else begin
      wb_instr_category   <= id_instr_category;
      if (id_stage_i.instr_done | id_stage_i.gen_stall_mem.instr_kill) begin
        id_instr_category_q <= id_instr_category;
        fcov_id_exc_int_q   <= fcov_id_exc_int;
      end
    end
  end


  // Check instruction categories calculated from instruction bits match what decoder has produced.

  // The ALU category is tricky as there's no specific ALU enable and instructions that actively use
  // the result of the ALU but aren't themselves ALU operations (such as load/store and JALR). This
  // categorizes anything that selects the ALU as the source of register write data and enables
  // register writes minus some exclusions as an ALU operation.
  `ASSERT(InstrCategoryALUCorrect, id_instr_category == InstrCategoryALU |->
      (id_stage_i.rf_wdata_sel == RF_WD_EX) && id_stage_i.rf_we_dec && ~id_stage_i.mult_sel_ex_o &&
      ~id_stage_i.div_sel_ex_o && ~id_stage_i.lsu_req_dec && ~id_stage_i.jump_in_dec)

  `ASSERT(InstrCategoryMulCorrect,
      id_instr_category == InstrCategoryMul |-> id_stage_i.mult_sel_ex_o)

  `ASSERT(InstrCategoryDivCorrect,
      id_instr_category == InstrCategoryDiv |-> id_stage_i.div_sel_ex_o)

  `ASSERT(InstrCategoryBranchCorrect,
      id_instr_category == InstrCategoryBranch |-> id_stage_i.branch_in_dec)

   `ASSERT(InstrCategoryJALCorrect,
      id_instr_category == InstrCategoryCJAL |->
         ((~id_stage_i.cheri_pmode_i & id_stage_i.jump_in_dec) || 
          (id_stage_i.cheri_pmode_i & id_stage_i.decoder_i.cheri_jal_en)))

   `ASSERT(InstrCategoryJALRCorrect,
      id_instr_category == InstrCategoryCJALR |->
         ((~id_stage_i.cheri_pmode_i & id_stage_i.jump_in_dec) || 
          (id_stage_i.cheri_pmode_i & id_stage_i.decoder_i.cheri_jalr_en)))

  `ASSERT(InstrCategoryLoadCorrect,
      id_instr_category == InstrCategoryLoad |-> id_stage_i.lsu_req_dec && !id_stage_i.lsu_we)

  `ASSERT(InstrCategoryStoreCorrect,
      id_instr_category == InstrCategoryStore |-> id_stage_i.lsu_req_dec && id_stage_i.lsu_we)

  `ASSERT(InstrCategoryCSRAccessCorrect,
      id_instr_category == InstrCategoryCSRAccess |-> id_stage_i.csr_access_o)
  `ASSERT(InstrCategoryEBreakDbgCorrect, id_instr_category == InstrCategoryEBreakDbg |->
      id_stage_i.ebrk_insn && id_stage_i.controller_i.ebreak_into_debug)

  `ASSERT(InstrCategoryEBreakExcCorrect, id_instr_category == InstrCategoryEBreakExc |->
      id_stage_i.ebrk_insn && !id_stage_i.controller_i.ebreak_into_debug)

  `ASSERT(InstrCategoryECallCorrect,
      id_instr_category == InstrCategoryECall |-> id_stage_i.ecall_insn_dec)

  `ASSERT(InstrCategoryMRetCorrect,
      id_instr_category == InstrCategoryMRet |-> id_stage_i.mret_insn_dec)

  `ASSERT(InstrCategoryDRetCorrect,
      id_instr_category == InstrCategoryDRet |-> id_stage_i.dret_insn_dec)

  `ASSERT(InstrCategoryWFICorrect,
      id_instr_category == InstrCategoryWFI |-> id_stage_i.wfi_insn_dec)

  `ASSERT(InstrCategoryFenceICorrect,
      id_instr_category == InstrCategoryFenceI && id_stage_i.instr_first_cycle |->
      id_stage_i.icache_inval_o)



  id_stall_type_e id_stall_type;

  // Set `id_stall_type` to the appropriate type based on signals in the ID/EX stage
  always_comb begin
    id_stall_type = IdStallTypeNone;

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.stall_mem) begin
        id_stall_type = IdStallTypeMem;
      end

      if (id_stage_i.stall_ld_hz) begin
        id_stall_type = IdStallTypeLdHz;
      end

      if (id_stage_i.stall_multdiv || id_stage_i.stall_branch ||
          id_stage_i.stall_jump || id_stage_i.stall_cheri) begin
        id_stall_type = IdStallTypeInstr;
      end

      if (id_stage_i.stall_cheri_trvk) begin
        id_stall_type = IdStallTypeTRVK;
      end
    end
  end

  // IF specific state enum
  typedef enum {
    IFStageFullAndFetching,
    IFStageFullAndIdle,
    IFStageEmptyAndFetching,
    IFStageEmptyAndIdle
  } if_stage_state_e;

  // ID/EX and WB have the same state enum
  // QQQ should we add exception state here??
  typedef enum {
    PipeStageFullAndStalled,
    PipeStageFullAndUnstalled,
    PipeStageEmpty
  } pipe_stage_state_e;

  if_stage_state_e   if_stage_state;
  pipe_stage_state_e id_stage_state;
  pipe_stage_state_e wb_stage_state;

  always_comb begin
    if_stage_state = IFStageEmptyAndIdle;

    if (if_stage_i.if_instr_valid) begin
      if (if_stage_i.req_i) begin
        if_stage_state = IFStageFullAndFetching;
      end else begin
        if_stage_state = IFStageFullAndIdle;
      end
    end else if(if_stage_i.req_i) begin
      if_stage_state = IFStageEmptyAndFetching;
    end
  end

  always_comb begin
    id_stage_state = PipeStageEmpty;

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.id_in_ready_o) begin
        id_stage_state = PipeStageFullAndUnstalled;
      end else begin
        id_stage_state = PipeStageFullAndStalled;
      end
    end
  end

  always_comb begin
    wb_stage_state = PipeStageEmpty;

    if (wb_stage_i.fcov_wb_valid) begin
      if (wb_stage_i.ready_wb_o) begin
        wb_stage_state = PipeStageFullAndUnstalled;
      end else begin
        wb_stage_state = PipeStageFullAndStalled;
      end
    end
  end

  // This latch is needed because if we cannot register this condition being true
  // with a clock. Being in the sleep mode implies that we don't have an active clock.
  // So, we need to catch the condition, latch it and keep it until we wake up and decode
  // an instruction (which guarantees we have a clock in the core)
  logic kept_wfi_with_irq;

  always_latch begin
    if (id_stage_i.controller_i.ctrl_fsm_cs == DECODE) begin
      kept_wfi_with_irq = 1'b0;
    end else if (id_stage_i.controller_i.ctrl_fsm_cs == SLEEP &&
                 id_stage_i.controller_i.ctrl_fsm_ns == SLEEP &&
                 (|cs_registers_i.mip)) begin
      kept_wfi_with_irq = 1'b1;
    end
  end

  logic instr_id_matches_trigger_d, instr_id_matches_trigger_q;

  assign instr_id_matches_trigger_d = id_stage_i.controller_i.trigger_match_i &&
                                      id_stage_i.controller_i.fcov_debug_entry_if;

  // Delay instruction matching trigger point since it is catched in IF stage.
  // We would want to cross it with decoded instruction categories and it does not matter
  // when exactly we are hitting the condition.
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_id_matches_trigger_q <= 1'b0;
    end else begin
      instr_id_matches_trigger_q <= instr_id_matches_trigger_d;
    end
  end

  // Keep track of previous data addr of Store to catch RAW hazard caused by STORE->LOAD
  logic [31:0]     prev_store_addr;
  logic [31:0]     data_addr_incr;
  logic [31:0]     curr_data_addr;
  logic            raw_hz;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_store_addr <= 1'b0;
    end else if (load_store_unit_i.data_we_o) begin
      // It does not matter if the store we executed before load is misaligned or not. Because
      // even if it is misaligned, we would catch the "corrected" version (2nd access) before
      // doing the RAW hazard check.
      prev_store_addr <= load_store_unit_i.data_addr_o;
    end
  end

  // Calculate the corrected version of the new data addr at the same time while LOAD instruction
  // gets decoded.
  always_comb begin
    if (load_store_unit_i.split_misaligned_access) begin
      data_addr_incr = load_store_unit_i.data_addr + 4;
      curr_data_addr = {data_addr_incr[2+:30],2'b00};
    end else begin
      curr_data_addr = load_store_unit_i.data_addr;
    end
  end

  // If we have LOAD at ID/EX stage and STORE at WB stage, compare the calculated address for LOAD
  // and the saved STORE address. If they are matching we would have RAW hazard.
  assign raw_hz = wb_stage_i.outstanding_store_wb_o &&
                  id_instr_category == InstrCategoryLoad &&
                  prev_store_addr == curr_data_addr;

  // Collect all the interrupts for collecting them in different bins.
  logic [5:0] fcov_irqs;

//  assign fcov_irqs = {id_stage_i.controller_i.irq_nm_ext_i,
//                      id_stage_i.controller_i.irq_nm_int,
  assign fcov_irqs = {id_stage_i.controller_i.irq_nm_i,
                      (|id_stage_i.controller_i.irqs_i.irq_fast),
                      id_stage_i.controller_i.irqs_i.irq_external,
                      id_stage_i.controller_i.irqs_i.irq_software,
                      id_stage_i.controller_i.irqs_i.irq_timer};

  logic            instr_unstalled;
  logic            instr_unstalled_last;
  logic            id_stall_type_last_valid;
  id_stall_type_e  id_stall_type_last;
  instr_category_e id_instr_category_last;

  // Keep track of previous values for some signals. These are used for some of the crosses relating
  // to exception and debug entry. We want to cross different instruction categories and stalling
  // behaviour with exception and debug entry but signals indicating entry occur a cycle after the
  // relevant information is flushed from the pipeline.
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // First cycle out of reset there is no last stall, use valid bit to deal with this case
      id_stall_type_last_valid <= 1'b0;
      id_stall_type_last       <= IdStallTypeNone;
      instr_unstalled_last     <= 1'b0;
      id_instr_category_last   <= InstrCategoryNone;
    end else begin
      id_stall_type_last_valid <= 1'b1;
      id_stall_type_last       <= id_stall_type;
      instr_unstalled_last     <= instr_unstalled;
      id_instr_category_last   <= id_instr_category;
    end
  end

  assign instr_unstalled =
    (id_stall_type == IdStallTypeNone) && (id_stall_type_last != IdStallTypeNone) &&
    id_stall_type_last_valid;

  // V2S Related Probes for Top-Level
  logic rf_we_glitch_err;
  logic lockstep_glitch_err;

  logic fcov_tag_clear_cs1cd;
  assign fcov_tag_clear_cs1cd = g_cheri_ex.u_cheri_ex.rf_fullcap_a.valid & 
                               ~g_cheri_ex.u_cheri_ex.result_cap_o.valid;

  // representablility and bound check cases
  logic [2:0]  fcov_cd_cs1_repr_cases;
  logic [2:0]  fcov_cd_pcc_repr_cases;

  assign fcov_cd_cs1_repr_cases = repr_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_a, g_cheri_ex.u_cheri_ex.result_data_o);
  assign fcov_cd_pcc_repr_cases = repr_cases(pcc2fullcap(cs_registers_i.pcc_cap_o), g_cheri_ex.u_cheri_ex.result_data_o);

  // address range representation
  // let's use # of 0's now - will change if figoure out something better QQQ
  logic [5:0] fcov_cs1_address_0cnt, fcov_cs2_address_0cnt, fcov_cd_address_0cnt;

  assign      fcov_cs1_address_0cnt = count32_zeros(g_cheri_ex.u_cheri_ex.rf_rdata_a);
  assign      fcov_cs2_address_0cnt = count32_zeros(g_cheri_ex.u_cheri_ex.rf_rdata_b);
  assign      fcov_cd_address_0cnt  = count32_zeros(g_cheri_ex.u_cheri_ex.result_data_o);

 
  logic [8:0] fcov_cjal_target_bound_cases;
  assign fcov_cjal_target_bound_cases = bound_check_cases(pcc2fullcap(cs_registers_i.pcc_cap_o), 
                                                        g_cheri_ex.u_cheri_ex.branch_target_o); 

  logic [8:0] fcov_cjalr_target_bound_cases;
  assign fcov_cjalr_target_bound_cases = bound_check_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_a,
                                                         g_cheri_ex.u_cheri_ex.branch_target_o); 
  
  logic [8:0] fcov_branch_target_bound_cases;
  assign fcov_branch_target_bound_cases = bound_check_cases(pcc2fullcap(cs_registers_i.pcc_cap_o), 
                                                          ex_block_i.branch_target_o[31:0]); 

  logic [8:0] fcov_clsc_bound_cases;
  assign fcov_clsc_bound_cases = bound_check_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_a,
                                                 g_cheri_ex.u_cheri_ex.cheri_ls_chkaddr); 
  
  logic [3:0] fcov_seal_bound_cases;
  logic [8:0] tmp9;
  assign tmp9 = bound_check_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_b, g_cheri_ex.u_cheri_ex.cheri_ls_chkaddr); 
  
  assign fcov_seal_bound_cases = tmp9[3:0];

  logic [4:0] fcov_setbounds_cases;
  assign fcov_setbounds_cases = setbounds_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_a, g_cheri_ex.u_cheri_ex.rf_rdata_a,
                                               g_cheri_ex.u_cheri_ex.rf_rdata_b);
  
  logic [4:0] fcov_setboundsimm_cases;
  assign fcov_setboundsimm_cases = setbounds_cases(g_cheri_ex.u_cheri_ex.rf_fullcap_a, g_cheri_ex.u_cheri_ex.rf_rdata_a,
                                                   g_cheri_ex.u_cheri_ex.cheri_imm12_i);

  logic [5:0] fcov_rs1_bitsize;
  assign fcov_rs1_bitsize = get_size(g_cheri_ex.u_cheri_ex.rf_rdata_a);

  logic fcov_id_error, fcov_wb_err;
  assign fcov_id_error = id_stage_i.controller_i.instr_fetch_err_prio | id_stage_i.controller_i.illegal_insn_prio |
                         id_stage_i.controller_i.ecall_insn_prio      | id_stage_i.controller_i.ebrk_insn_prio |
                         id_stage_i.controller_i.cheri_ex_err_prio    | id_stage_i.controller_i.cheri_ex_err_prio |
                         id_stage_i.controller_i.cheri_asr_err_prio;
  assign fcov_wb_error = id_stage_i.controller_i.load_err_prio | id_stage_i.controller_i.store_err_prio |
                         id_stage_i.controller_i.cheri_wb_err_prio;

 
 
  covergroup uarch_cg @(posedge clk_i);
    option.per_instance = 1;
    option.name = "uarch_cg";

    ///////////////////
    // Coverage points
    ///////////////////

    cp_id_instr_category: coverpoint id_instr_category {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_id_instr_category_last: coverpoint id_instr_category_last {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_stall_type_id: coverpoint id_stall_type;

    cp_wb_reg_no_load_hz: coverpoint id_stage_i.fcov_rf_rd_wb_hz &&
                                     !wb_stage_i.outstanding_load_wb_o;

    cp_mem_raw_hz: coverpoint raw_hz;

    cp_mprv: coverpoint cs_registers_i.mstatus_q.mprv;

    // ls err: mem_err, pmp_err, cheri_err
    cp_ls_exception: coverpoint load_store_unit_i.lsu_dv_ext_i.fcov_ls_exception_type;

    cp_branch_taken: coverpoint id_stage_i.fcov_branch_taken;
    cp_branch_not_taken: coverpoint id_stage_i.fcov_branch_not_taken;

    // KLIU - for CHERIoT priv mode doesn't matter
    cp_priv_mode_id: coverpoint priv_mode_id {
      ignore_bins  ignore  = {PRIV_LVL_U};
      illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
    }
    cp_priv_mode_lsu: coverpoint priv_mode_lsu {
      ignore_bins  ignore  = {PRIV_LVL_U};
      illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
    }

    cp_if_stage_state : coverpoint if_stage_state;
    cp_id_stage_state : coverpoint id_stage_state;
    cp_wb_stage_state : coverpoint wb_stage_state;

    // V2S Coverpoints
    cp_data_ind_timing: coverpoint cs_registers_i.data_ind_timing_o;
    cp_data_ind_timing_instr: coverpoint id_instr_category iff (cs_registers_i.data_ind_timing_o) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_dummy_instr_en: coverpoint cs_registers_i.dummy_instr_en_o;
    cp_dummy_instr_mask: coverpoint cs_registers_i.dummy_instr_mask_o;
    cp_dummy_instr_type: coverpoint if_stage_i.if_stage_dv_ext_i.fcov_dummy_instr_type;
    cp_dummy_instr: coverpoint id_instr_category iff (cs_registers_i.dummy_instr_en_o) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    // Each stage sees a dummy instruction.
    cp_dummy_instr_if_stage: coverpoint if_stage_i.if_stage_dv_ext_i.fcov_insert_dummy_instr;
    cp_dummy_instr_id_stage: coverpoint if_stage_i.dummy_instr_id_o;
    //cp_dummy_instr_wb_stage: coverpoint wb_stage_i.dummy_instr_wb_o;  // QQQ why need this?

    `DV_FCOV_EXPR_SEEN(rf_a_ecc_err, ibex_core_dv_ext_i.fcov_rf_ecc_err_a_id)
    `DV_FCOV_EXPR_SEEN(rf_b_ecc_err, ibex_core_dv_ext_i.fcov_rf_ecc_err_b_id)

//    `DV_FCOV_EXPR_SEEN(icache_ecc_err, if_stage_i.icache_ecc_error_o)

    // QQQ maybe better to leave integ check at top/lock-step level
    //`DV_FCOV_EXPR_SEEN(mem_load_ecc_err, load_store_unit_i.load_resp_intg_err_o)
    //`DV_FCOV_EXPR_SEEN(mem_store_ecc_err, load_store_unit_i.store_resp_intg_err_o)

//    `DV_FCOV_EXPR_SEEN(lockstep_err, lockstep_glitch_err)
//    `DV_FCOV_EXPR_SEEN(rf_we_glitch_err, rf_we_glitch_err)
//    `DV_FCOV_EXPR_SEEN(pc_mismatch_err, if_stage_i.pc_mismatch_alert_o)

    cp_fetch_enable: coverpoint fetch_enable_i {
      // bins fetch_on    = {IbexMuBiOn};
      // bins fetch_off   = {IbexMuBiOff};
      bins fetch_on    = {FetchEnableOn};
      bins fetch_off   = {FetchEnableOff};
      bins fetch_inval = default;
    }

    // TODO: MRET/WFI in debug mode?
    // Specific cover points for these as `id_instr_category` will be InstrCategoryPrivIllegal when
    // executing these instructions in U-mode.
    `DV_FCOV_EXPR_SEEN(mret_in_umode, id_stage_i.mret_insn_dec && priv_mode_id == PRIV_LVL_U)
    `DV_FCOV_EXPR_SEEN(wfi_in_umode, id_stage_i.wfi_insn_dec && priv_mode_id == PRIV_LVL_U)

    // Unsupported writes to WARL type CSRs
    `DV_FCOV_EXPR_SEEN(warl_check_mstatus,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_mstatus_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mie,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_mie_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mtvec,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_mtvec_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mepc,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_mepc_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mtval,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_mtval_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_dcsr,
                       ibex_core_dv_ext_i.fcov_csr_write &&
                       (cs_registers_i.u_dcsr_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    // QQQ this got renamed in ibex?
    //`DV_FCOV_EXPR_SEEN(warl_check_cpuctrl,
    //                   ibex_core_dv_ext_i.fcov_csr_write &&
    //                   (cs_registers_i.u_cpuctrlsts_part_csr.wr_data_i !=
    //                   cs_registers_i.csr_wdata_int))

//    `DV_FCOV_EXPR_SEEN(double_fault, cs_registers_i.cpuctrlsts_part_d.double_fault_seen)
//    `DV_FCOV_EXPR_SEEN(icache_enable, cs_registers_i.cpuctrlsts_part_d.icache_enable)

    cp_irq_pending: coverpoint id_stage_i.irq_pending_i | id_stage_i.irq_nm_i;
    cp_debug_req: coverpoint id_stage_i.controller_i.fcov_debug_req;

    cp_csr_read_only: coverpoint cs_registers_i.csr_addr_i iff (ibex_core_dv_ext_i.fcov_csr_read_only) {
      ignore_bins ignore = {`IGNORED_CSRS};
    }

    cp_csr_write: coverpoint cs_registers_i.csr_addr_i iff (ibex_core_dv_ext_i.fcov_csr_write) {
      ignore_bins ignore = {`IGNORED_CSRS};
    }

    `DV_FCOV_EXPR_SEEN(csr_invalid_read_only, ibex_core_dv_ext_i.fcov_csr_read_only && cs_registers_i.illegal_csr)
    `DV_FCOV_EXPR_SEEN(csr_invalid_write, ibex_core_dv_ext_i.fcov_csr_write && cs_registers_i.illegal_csr)

    cp_debug_mode: coverpoint debug_mode;

    `DV_FCOV_EXPR_SEEN(debug_wakeup, id_stage_i.controller_i.controller_dv_ext_i.fcov_debug_wakeup)
    `DV_FCOV_EXPR_SEEN(all_debug_req, id_stage_i.controller_i.controller_dv_ext_i.fcov_all_debug_req)
    `DV_FCOV_EXPR_SEEN(debug_entry_if, id_stage_i.controller_i.controller_dv_ext_i.fcov_debug_entry_if)
    `DV_FCOV_EXPR_SEEN(debug_entry_id, id_stage_i.controller_i.controller_dv_ext_i.fcov_debug_entry_id)
    `DV_FCOV_EXPR_SEEN(pipe_flush, id_stage_i.controller_i.controller_dv_ext_i.fcov_pipe_flush)
    `DV_FCOV_EXPR_SEEN(single_step_taken, id_stage_i.controller_i.controller_dv_ext_i.fcov_debug_single_step_taken)
    `DV_FCOV_EXPR_SEEN(single_step_exception, id_stage_i.controller_i.do_single_step_d &&
                                              id_stage_i.controller_i.controller_dv_ext_i.fcov_pipe_flush)
    `DV_FCOV_EXPR_SEEN(insn_trigger_enter_debug, instr_id_matches_trigger_q)

    cp_nmi_taken: coverpoint ((fcov_irqs[5] || fcov_irqs[4])) iff
                             (id_stage_i.controller_i.fcov_interrupt_taken);

    cp_interrupt_taken: coverpoint fcov_irqs iff (id_stage_i.controller_i.fcov_interrupt_taken){
      wildcard bins nmi_external  = {6'b1?????};
      wildcard bins nmi_internal  = {6'b01????};
      wildcard bins irq_fast      = {6'b001???};
      wildcard bins irq_external  = {6'b0001??};
      wildcard bins irq_software  = {6'b00001?};         // QQQ - let's worry about different interrupt sources later
      wildcard bins irq_timer     = {6'b000001};
      // ignore_bins ignore = default;
    }

    cp_controller_fsm: coverpoint id_stage_i.controller_i.ctrl_fsm_cs {
      bins out_of_reset = (RESET => BOOT_SET);
      bins out_of_boot_set = (BOOT_SET => FIRST_FETCH);
      bins out_of_first_fetch0 = (FIRST_FETCH => DECODE);
      bins out_of_first_fetch1 = (FIRST_FETCH => IRQ_TAKEN);
      bins out_of_first_fetch2 = (FIRST_FETCH => DBG_TAKEN_IF);
      bins out_of_decode0 = (DECODE => FLUSH);
      bins out_of_decode1 = (DECODE => DBG_TAKEN_IF);
      bins out_of_decode2 = (DECODE => IRQ_TAKEN);
      bins out_of_irq_taken = (IRQ_TAKEN => DECODE);
      bins out_of_debug_taken_if = (DBG_TAKEN_IF => DECODE);
      bins out_of_debug_taken_id = (DBG_TAKEN_ID => DECODE);
      bins out_of_flush0 = (FLUSH => DECODE);
      bins out_of_flush1 = (FLUSH => DBG_TAKEN_ID);
      bins out_of_flush2 = (FLUSH => WAIT_SLEEP);
      bins out_of_flush3 = (FLUSH => DBG_TAKEN_IF);
      bins out_of_wait_sleep = (WAIT_SLEEP => SLEEP);
      bins out_of_sleep = (SLEEP => FIRST_FETCH);
      // TODO: VCS does not implement default sequence so illegal_bins will be empty
      // illegal_bins illegal_transitions = default sequence;
    }

    cp_controller_fsm_sleep: coverpoint id_stage_i.controller_i.ctrl_fsm_cs {
      bins out_of_sleep = (SLEEP => FIRST_FETCH);
      bins enter_sleep = (WAIT_SLEEP => SLEEP);
      // TODO: VCS does not implement default sequence so illegal_bins will be empty
      // illegal_bins illegal_transitions = default sequence;
    }

    // This will only be seen when specific interrupt is disabled by MIE CSR
    `DV_FCOV_EXPR_SEEN(irq_continue_sleep, kept_wfi_with_irq)

    cp_single_step_instr: coverpoint id_instr_category iff
                             (id_stage_i.controller_i.controller_dv_ext_i.fcov_debug_single_step_taken) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal =
        {InstrCategoryOther, InstrCategoryNone, InstrCategoryOtherIllegal
         // [Debug Spec v1.0.0-STABLE, p.95]
         // > dret is an instruction which only has meaning while Debug Mode
         // We want to step over this to at-least specify how the Ibex does behave.
         //
         // [Debug Spec v1.0.0-STABLE, p.50]
         // > If the instruction being stepped over is wfi and would normally stall the hart,
         // > then instead the instruction is treated as nop.
         // Again this will be useful coverage to verify we are testing this behaviour.
        };
    }

    // Only sample the bus error from the first access of misaligned load/store when we are in
    // the data phase of the second access. Without this, we cannot sample the case when both
    // first and second access fails.
    cp_misaligned_first_data_bus_err: coverpoint load_store_unit_i.lsu_dv_ext_i.fcov_mis_bus_err_1_q iff
      (load_store_unit_i.lsu_dv_ext_i.fcov_mis_rvalid_2);

    cp_misaligned_second_data_bus_err: coverpoint load_store_unit_i.data_err_i iff
      (load_store_unit_i.lsu_dv_ext_i.fcov_mis_rvalid_2);

    misaligned_data_bus_err_cross: cross cp_misaligned_first_data_bus_err,
                                         cp_misaligned_second_data_bus_err;
   // {
      // Cannot see both bus errors together as they're signalled at different states of the load
      // store unit FSM -- QQQ this isn't true when rvalid1 and rvalid2 are >=1 cycles apart?
      // illegal_bins illegal = binsof(cp_misaligned_first_data_bus_err) intersect {1'b1} &&
      //  binsof(cp_misaligned_second_data_bus_err) intersect {1'b1};
   // }
    
    //
    // New coverage points
    //

    cp_rs1_regaddr: coverpoint id_stage_i.rf_raddr_a_o[4:0] iff (id_stage_i.rf_ren_a) {
      bins bin0      = {0};
      bins bin1to14  = {[1:14]};
      bins bin15     = {15};
      bins bin16to31 = {[16:31]};   // for CHERIoT negative case
    }

    cp_rs2_regaddr: coverpoint id_stage_i.rf_raddr_b_o[4:0] iff (id_stage_i.rf_ren_b) {
      bins bin0      = {0};
      bins bin1to14  = {[1:14]};
      bins bin15     = {15};
      bins bin16to31 = {[16:31]};   // for CHERIoT negative case
    }
 
    cp_rd_regaddr:  coverpoint id_stage_i.rf_waddr_id_o[4:0] iff 
                 (id_stage_i.rf_we_id_o | g_cheri_ex.u_cheri_ex.cheri_rf_we_o) {
      bins bin0      = {0};
      bins bin1to14  = {[1:14]};
      bins bin15     = {15};
      bins bin16to31 = {[16:31]};   // for CHERIoT negative case
    }

    // for cincaddr rs2 argument
    cp_rs2_as_inc: coverpoint g_cheri_ex.u_cheri_ex.rf_rdata_b {
      bins bin1 ={0};
      bins bin2 ={[1:32'h7fff_ffff]};
      bins bin3 ={32'h8000_0000};
      bins bin4 ={[32'h8000_0001:32'hffff_fffe]};
      bins bin5 ={32'hffff_ffff};
    }

    // all CHERIoT instructions enumerated
    cp_cheri_instr_set: coverpoint fcov_cheri_instr iff ((|cheri_ops) && g_cheri_ex.u_cheri_ex.cheri_exec_id_i);
     
    // coverage points for PCC
    cp_pcc_tag: coverpoint cs_registers_i.pcc_cap_o.valid;

    cp_pcc_exp: coverpoint cs_registers_i.pcc_cap_o.exp iff (cs_registers_i.pcc_cap_o.valid) {
      bins bin0 = {0};
      bins bin1 = {[1:14]};
      bins bin2 = {24};
      illegal_bins illegal = default;
    }

    // valid pcc now will always have otype == 0 and perm_ex set (assertion in cs_reg_dv_ext)
    cp_pcc_perm_asr: coverpoint cs_registers_i.pcc_cap_o.perms[PERM_SR];
    cp_pcc_perm_ex: coverpoint cs_registers_i.pcc_cap_o.perms[PERM_EX];


    // cheriot instruction immediates
    cp_cheri_imm20: coverpoint g_cheri_ex.u_cheri_ex.cheri_imm20_i {
      bins bin1 ={0};
      bins bin2 ={[1:20'h7_ffff]};
      bins bin3 ={20'h8_0000};
      bins bin4 ={[20'h8_0001:20'hf_fffe]};
      bins bin5 ={20'hf_ffff};
     }

    cp_cheri_imm12: coverpoint g_cheri_ex.u_cheri_ex.cheri_imm12_i {
      bins bin1 ={0};
      bins bin2 ={[1:12'h7ff]};
      bins bin3 ={12'h800};
      bins bin4 ={[12'h801:12'hffe]};
      bins bin5 ={12'hfff};
    }


    // coverage points for CS1
    cp_cs1_tag: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.valid;

    cp_cs1_exp: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.exp {
      bins bin0 = {0};
      bins bin1 = {[1:14]};
      bins bin2 = {24};
    }

    cp_cs1_otype: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.otype {
      bins bin[] = {[0:7]};    // including reserved values for coverage
    }

    cp_cs1_sealed: coverpoint ~(|g_cheri_ex.u_cheri_ex.rf_fullcap_a.otype) iff 
                              (g_cheri_ex.u_cheri_ex.rf_fullcap_a.valid);

    cp_cs1_cor: coverpoint {g_cheri_ex.u_cheri_ex.rf_fullcap_a.base_cor, 
                            g_cheri_ex.u_cheri_ex.rf_fullcap_a.top_cor} {
      bins bin0 = {4'b0000}; 
      bins bin1 = {4'b0001}; 
      // bins bin2 = {4'b0011}; // base_cor = 0, top_cor = -1, impossible case
      bins bin3 = {4'b1100}; 
      // bins bin4 = {4'b1101};    // impossible case
      bins bin5 = {4'b1111};    
    }

    cp_cs1_top: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.top {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cs1_base: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.base {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cs1_perms: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.perms {
      wildcard bins gl0  = {13'b?_????_????_???0}; 
      wildcard bins gl1  = {13'b?_????_????_???1};
      wildcard bins lg0  = {13'b?_????_????_??0?};
      wildcard bins lg1  = {13'b?_????_????_??1?};
      wildcard bins sd0  = {13'b?_????_????_?0??};
      wildcard bins sd1  = {13'b?_????_????_?1??};
      wildcard bins lm0  = {13'b?_????_????_0???}; 
      wildcard bins lm1  = {13'b?_????_????_1???};
      wildcard bins sl0  = {13'b?_????_???0_????}; 
      wildcard bins sl1  = {13'b?_????_???1_????};
      wildcard bins ld0  = {13'b?_????_??0?_????}; 
      wildcard bins ld1  = {13'b?_????_??1?_????};
      wildcard bins mc0  = {13'b?_????_?0??_????}; 
      wildcard bins mc1  = {13'b?_????_?1??_????};
      wildcard bins sr0  = {13'b?_????_0???_????}; 
      wildcard bins sr1  = {13'b?_????_1???_????};
      wildcard bins ex0  = {13'b?_???0_????_????}; 
      wildcard bins ex1  = {13'b?_???1_????_????};
      wildcard bins us0  = {13'b?_??0?_????_????}; 
      wildcard bins us1  = {13'b?_??1?_????_????};
      wildcard bins se0  = {13'b?_?0??_????_????}; 
      wildcard bins se1  = {13'b?_?1??_????_????};
      wildcard bins u00  = {13'b?_0???_????_????}; 
      wildcard bins u01  = {13'b?_1???_????_????};
      wildcard bins u10  = {13'b0_????_????_????}; 
      wildcard ignore_bins u11 = {13'b1_????_????_????};
      illegal_bins illegal = default;
    }

    cp_cs1_perms_load: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.perms {
      wildcard bins lg0  = {13'b?_????_????_??0?};
      wildcard bins lg1  = {13'b?_????_????_??1?};
      wildcard bins lm0  = {13'b?_????_????_0???}; 
      wildcard bins lm1  = {13'b?_????_????_1???};
      wildcard bins ld0  = {13'b?_????_??0?_????}; 
      wildcard bins ld1  = {13'b?_????_??1?_????};
      wildcard bins mc0  = {13'b?_????_?0??_????}; 
      wildcard bins mc1  = {13'b?_????_?1??_????};
    }

    cp_cs1_perms_store: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.perms {
      wildcard bins sd0  = {13'b?_????_????_?0??};
      wildcard bins sd1  = {13'b?_????_????_?1??};
      wildcard bins sl0  = {13'b?_????_???0_????}; 
      wildcard bins sl1  = {13'b?_????_???1_????};
      wildcard bins mc0  = {13'b?_????_?0??_????}; 
      wildcard bins mc1  = {13'b?_????_?1??_????};
    }

    cp_cs1_perm_ex: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.perms[PERM_EX];
    cp_cs1_perm_gl: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.perms[PERM_GL];

    cp_cs1_address: coverpoint fcov_cs1_address_0cnt {
      bins valid[]       = {[0:32]};
      ignore_bins ignore = {[33:$]};
    }

    cp_cs1_base32: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.base32 {
      bins bin0   = {0};
      bins bin1   = {[1: 32'hffff_fffd]};
      bins bin2   = {[1: 32'hffff_fffe]};
      bins bin3   = {32'hffff_ffff};
    }

    cp_cs1_top33: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_a.top33 {
      bins bin0   = {0};
      bins bin1   = {[1: 33'hffff_fffe]};
      bins bin2   = {33'hffff_ffff};
      bins bin3   = {33'h1_0000_0000};
    }

    cp_rs2_perm_mask: coverpoint g_cheri_ex.u_cheri_ex.rf_rdata_b[12:0] {
      wildcard bins gl0  = {13'b?_????_????_???0}; 
      wildcard bins gl1  = {13'b?_????_????_???1};
      wildcard bins lg0  = {13'b?_????_????_??0?};
      wildcard bins lg1  = {13'b?_????_????_??1?};
      wildcard bins sd0  = {13'b?_????_????_?0??};
      wildcard bins sd1  = {13'b?_????_????_?1??};
      wildcard bins lm0  = {13'b?_????_????_0???}; 
      wildcard bins lm1  = {13'b?_????_????_1???};
      wildcard bins sl0  = {13'b?_????_???0_????}; 
      wildcard bins sl1  = {13'b?_????_???1_????};
      wildcard bins ld0  = {13'b?_????_??0?_????}; 
      wildcard bins ld1  = {13'b?_????_??1?_????};
      wildcard bins mc0  = {13'b?_????_?0??_????}; 
      wildcard bins mc1  = {13'b?_????_?1??_????};
      wildcard bins sr0  = {13'b?_????_0???_????}; 
      wildcard bins sr1  = {13'b?_????_1???_????};
      wildcard bins ex0  = {13'b?_???0_????_????}; 
      wildcard bins ex1  = {13'b?_???1_????_????};
      wildcard bins us0  = {13'b?_??0?_????_????}; 
      wildcard bins us1  = {13'b?_??1?_????_????};
      wildcard bins se0  = {13'b?_?0??_????_????}; 
      wildcard bins se1  = {13'b?_?1??_????_????};
      wildcard bins u00  = {13'b?_0???_????_????}; 
      wildcard bins u01  = {13'b?_1???_????_????};
      wildcard bins u10  = {13'b0_????_????_????}; 
      wildcard ignore_bins u11 = {13'b1_????_????_????};
    }

    // coverage points for CS2. CS2 is only used for CSEAL/CUNSEAL, CSUB, CSEQX, CTESTSUBSET

    cp_cs2_tag: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.valid;

    cp_cs2_exp: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.exp {
      bins bin0 = {0};
      bins bin1 = {[1:14]};
      bins bin2 = {24};
    }

    cp_cs2_otype: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.otype {
      bins bin[] = {[0:7]};    // including reserved values for coverage
    }

    cp_cs2_sealed: coverpoint ~(|g_cheri_ex.u_cheri_ex.rf_fullcap_b.otype) iff 
                              (g_cheri_ex.u_cheri_ex.rf_fullcap_a.valid);

    cp_cs2_cor: coverpoint {g_cheri_ex.u_cheri_ex.rf_fullcap_b.base_cor, 
                            g_cheri_ex.u_cheri_ex.rf_fullcap_b.top_cor} {
      bins bin0 = {4'b0000}; 
      bins bin1 = {4'b0001}; 
      // bins bin2 = {4'b0011}; // base_cor = 0, top_cor = -1, impossible case
      bins bin3 = {4'b1100}; 
      // bins bin4 = {4'b1101};    // impossible case
      bins bin5 = {4'b1111};    
    }

    cp_cs2_top: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.top {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cs2_base: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.base {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cs2_perms: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.perms {
      wildcard bins gl0  = {13'b?_????_????_???0}; 
      wildcard bins gl1  = {13'b?_????_????_???1};
      wildcard bins lg0  = {13'b?_????_????_??0?};
      wildcard bins lg1  = {13'b?_????_????_??1?};
      wildcard bins sd0  = {13'b?_????_????_?0??};
      wildcard bins sd1  = {13'b?_????_????_?1??};
      wildcard bins lm0  = {13'b?_????_????_0???}; 
      wildcard bins lm1  = {13'b?_????_????_1???};
      wildcard bins sl0  = {13'b?_????_???0_????}; 
      wildcard bins sl1  = {13'b?_????_???1_????};
      wildcard bins ld0  = {13'b?_????_??0?_????}; 
      wildcard bins ld1  = {13'b?_????_??1?_????};
      wildcard bins mc0  = {13'b?_????_?0??_????}; 
      wildcard bins mc1  = {13'b?_????_?1??_????};
      wildcard bins sr0  = {13'b?_????_0???_????}; 
      wildcard bins sr1  = {13'b?_????_1???_????};
      wildcard bins ex0  = {13'b?_???0_????_????}; 
      wildcard bins ex1  = {13'b?_???1_????_????};
      wildcard bins us0  = {13'b?_??0?_????_????}; 
      wildcard bins us1  = {13'b?_??1?_????_????};
      wildcard bins se0  = {13'b?_?0??_????_????}; 
      wildcard bins se1  = {13'b?_?1??_????_????};
      wildcard bins u00  = {13'b?_0???_????_????}; 
      wildcard bins u01  = {13'b?_1???_????_????};
      wildcard bins u10  = {13'b0_????_????_????}; 
      wildcard ignore_bins u11 = {13'b1_????_????_????};
      illegal_bins illegal = default;
    }

    cp_cs2_perm_gl: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.perms[PERM_GL];
    cp_cs2_perm_se: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.perms[PERM_SE];
    cp_cs2_perm_us: coverpoint g_cheri_ex.u_cheri_ex.rf_fullcap_b.perms[PERM_US];

    cp_cs2_address: coverpoint fcov_cs2_address_0cnt {
      bins valid[]       = {[0:32]};
      ignore_bins ignore = {[33:$]};
    }

    cp_cs2_seal_type: coverpoint g_cheri_ex.u_cheri_ex.rf_rdata_b {
      bins bin_hi   = {[16:$]};
      bins bin_mi[] = {[8:15]};           // seal otype 8:15
      bins bin_lo[] = {[0:7]};            // seal otype 0:7
    }


    // coverage points for CD
    cp_cd_tag: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.valid;

    cp_cd_exp: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.exp {
      bins bin0 = {0};
      bins bin1 = {[1:14]};
      bins bin2 = {24};
    }

    cp_cd_otype: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.otype {
      bins bin[] = {[0:7]};    // including reserved values for coverage
    }

    cp_cd_cor: coverpoint {g_cheri_ex.u_cheri_ex.result_cap_o.base_cor, 
                           g_cheri_ex.u_cheri_ex.result_cap_o.top_cor} {
      bins bin0 = {4'b0000}; 
      bins bin1 = {4'b0001}; 
      // bins bin2 = {4'b0011}; 
      bins bin3 = {4'b1100}; 
      // bins bin4 = {4'b1101}; 
      bins bin5 = {4'b1111}; 
    }

   cp_cd_top: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.top {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cd_base: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.base {
      bins bin_all1 = {9'h1ff};
      bins bin_all0 = {9'h0};
      bins bin1     = {[9'h1:9'h1fe]};
    }

    cp_cd_cperms: coverpoint g_cheri_ex.u_cheri_ex.result_cap_o.cperms;

    cp_cd_address: coverpoint fcov_cd_address_0cnt {
      bins valid[]       = {[0:32]};
      ignore_bins ignore = {[33:$]};
    }


    // addr/perm violations. this may cause either tag clearing or exception
    cp_cheri_vio: coverpoint {g_cheri_ex.u_cheri_ex.perm_vio_vec, g_cheri_ex.u_cheri_ex.addr_bound_vio}  iff 
                            (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      wildcard bins bound = {10'b??_????_???1};
      wildcard bins tag   = {10'b??_????_??1?};
      wildcard bins seal  = {10'b??_????_?1??};
      wildcard bins ex    = {10'b??_????_1???};
      wildcard bins ld    = {10'b??_???1_????};
      wildcard bins sd    = {10'b??_??1?_????};
      wildcard bins sc    = {10'b??_?1??_????};
      wildcard bins sr    = {10'b??_1???_????};
      wildcard bins align = {10'b?1_????_????};
      wildcard bins slc   = {10'b1?_????_????};
    }

    cp_tag_clear_cs1cd: coverpoint fcov_tag_clear_cs1cd iff 
                                         (g_cheri_ex.u_cheri_ex.cheri_exec_id_i);

    // coverage points for exception conditions
    cp_cheri_wb_exception_causes: coverpoint g_cheri_ex.u_cheri_ex.cheri_err_cause iff
                                             (g_cheri_ex.u_cheri_ex.cheri_wb_err_d) {
      // bins bounds     = {5'h1};        // no bound violation reported by cheri_wb exception (coverted to fetch_err)
      bins tag        = {5'h2};
      bins seal       = {5'h3};
      bins perm_ex    = {5'h11};
      bins perm_sr    = {5'h18};
      bins other      = {5'h0};           // used for scr invalide address (treated as illegal instructions in RV32)
      illegal_bins illegal = default;
    }

    cp_cheri_clsc_exception_causes: coverpoint g_cheri_ex.u_cheri_ex.cheri_err_cause iff
                                              (g_cheri_ex.u_cheri_ex.cheri_lsu_req & g_cheri_ex.u_cheri_ex.cheri_lsu_err) {
      bins bounds     = {5'h1};
      bins tag        = {5'h2};
      bins seal       = {5'h3};
      bins perm_load  = {5'h12};
      bins perm_store = {5'h13};
      bins perm_sc    = {5'h15};
      bins other      = {5'h0};           // alignment error is reported as a different mcause/mtval code
      illegal_bins illegal = default;
    }

    cp_cheri_rv32lsu_exception_causes: coverpoint g_cheri_ex.u_cheri_ex.rv32_err_cause iff
                                                 (g_cheri_ex.u_cheri_ex.rv32_lsu_req_i & g_cheri_ex.u_cheri_ex.rv32_lsu_err) {
      bins bounds     = {5'h1};
      bins tag        = {5'h2};
      bins seal       = {5'h3};
      bins perm_load  = {5'h12};
      bins perm_store = {5'h13};
      illegal_bins illegal = default;
    }


    cp_cheri_exception_reg_id: coverpoint g_cheri_ex.u_cheri_ex.cheri_wb_err_info_d[9:5] iff
                          ((g_cheri_ex.u_cheri_ex.cheri_wb_err_d & !cheri_ops[CCSR_RW]) | 
                          (g_cheri_ex.u_cheri_ex.lsu_req_o & g_cheri_ex.u_cheri_ex.lsu_cheri_err_o )) {
      wildcard illegal_bins illegal = {5'b1????} ;
    }

    cp_scr_addr: coverpoint id_stage_i.rf_raddr_b_o[4:0] { 
      bins good[] = {[28:31]};  // ZTOPC goes to a separate interface
      bins bad    = {[0:23]};
      ignore_bins ignore = {[24:26]};    // debug SCR
    }

    cp_scr_read_only: coverpoint g_cheri_ex.u_cheri_ex.csr_addr_o iff (
                                 g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_scr_read_only) {
      bins good[] = {[28:31]};  // ZTOPC goes to a separate interface
      bins bad    = {[0:23]};
      ignore_bins ignore = {[24:26]};    // debug SCR
    }

    cp_scr_write: coverpoint g_cheri_ex.u_cheri_ex.csr_addr_o iff (
                             g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_scr_write) {
      bins good[] = {[28:31]};  // ZTOPC goes to a separate interface
      bins bad    = {[0:23]};
      ignore_bins ignore = {[24:26]};    // debug SCR
    }

    // QQQ need to add mtcc/mepcc related coverage

    cp_cpu_lsu_req: coverpoint g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_acc;

    cp_cpu_lsu_err: coverpoint g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_err;
 
    cp_lsu_xfer_size: coverpoint g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_ls_xfer_size iff 
                                 (g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_req) {
      bins good[] = {1, 2, 4, 8};
      illegal_bins illegal = default;
    }

    cp_ls_room_cs1_chk: coverpoint g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_ls_cap_room_chk iff 
                                   (g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_req) {
      bins good[] = {0, 1};
      bins bad    = {2};
      illegal_bins illegal = default;
    }

    cp_mshwm_set: coverpoint g_cheri_ex.u_cheri_ex.csr_mshwm_set_o;

    cp_stkz_stall1: coverpoint g_cheri_ex.u_cheri_ex.cpu_stkz_stall1 iff
                               (g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_req);
    cp_stkz_stall0: coverpoint g_cheri_ex.u_cheri_ex.cpu_stkz_stall0 iff
                               (g_cheri_ex.u_cheri_ex.cheri_ex_dv_ext_i.fcov_cpu_lsu_req);

    cp_sktz_err: coverpoint g_cheri_ex.u_cheri_ex.cpu_stkz_err;       // abort error (exception)

    cp_clsc_mem_err: coverpoint  load_store_unit_i.lsu_dv_ext_i.fcov_clsc_mem_err {
      illegal_bins illegal = {7};        // rsvd value
    }

    
    //
    // clc: loaded memory cap coverage
    //
    cp_clc_clrperm: coverpoint load_store_unit_i.resp_lc_clrperm_q[3:0] iff
                            (~load_store_unit_i.data_we_q & load_store_unit_i.lsu_resp_valid_o) {
      wildcard illegal_bins illegal = {4'b?1??};        // rsvd value
    }

    cp_clc_mem_cap_perms: coverpoint load_store_unit_i.lsu_dv_ext_i.fcov_clc_mem_cap.perms iff
                            (~load_store_unit_i.data_we_q & load_store_unit_i.lsu_resp_valid_o) {
      wildcard bins gl0  = {13'b?_????_????_???0}; 
      wildcard bins gl1  = {13'b?_????_????_???1};
      wildcard bins lg0  = {13'b?_????_????_??0?};
      wildcard bins lg1  = {13'b?_????_????_??1?};
      wildcard bins sd0  = {13'b?_????_????_?0??};
      wildcard bins sd1  = {13'b?_????_????_?1??};
      wildcard bins lm0  = {13'b?_????_????_0???}; 
      wildcard bins lm1  = {13'b?_????_????_1???};
    }
 
    cp_clc_mem_cap_valid: coverpoint load_store_unit_i.lsu_dv_ext_i.fcov_clc_mem_cap_valid iff
                            (~load_store_unit_i.data_we_q & load_store_unit_i.lsu_resp_valid_o); 

    cp_clc_mem_cap_exp: coverpoint load_store_unit_i.lsu_dv_ext_i.fcov_clc_mem_cap.exp iff
                            (~load_store_unit_i.data_we_q & load_store_unit_i.lsu_resp_valid_o) {
      bins bin0 = {0};
      bins bin1 = {[1:14]};
      bins bin2 = {24};
    }

    cp_clc_mem_cap_cor: coverpoint {load_store_unit_i.lsu_dv_ext_i.fcov_clc_mem_cap.top_cor,  
                                    load_store_unit_i.lsu_dv_ext_i.fcov_clc_mem_cap.base_cor} iff
                            (~load_store_unit_i.data_we_q & load_store_unit_i.lsu_resp_valid_o) {
      bins bin0 = {4'b0000}; 
      bins bin1 = {4'b0001}; 
      // bins bin2 = {4'b0011}; // base_cor = 0, top_cor = -1, impossible case
      bins bin3 = {4'b1100}; 
      // bins bin4 = {4'b1101};    // impossible case
      bins bin5 = {4'b1111};    
    }

    cp_cheri_fetch_tag_vio: coverpoint id_stage_i.instr_fetch_cheri_acc_vio_i iff
                                      (id_stage_i.instr_valid_i);
    cp_cheri_fetch_bound_vio: coverpoint id_stage_i.instr_fetch_cheri_bound_vio_i iff
                                      (id_stage_i.instr_valid_i);

    cp_trvk_addr: coverpoint g_trvk_stage.cheri_trvk_stage_i.rf_trvk_addr_o[3:0] iff 
                             (g_trvk_stage.cheri_trvk_stage_i.rf_trvk_en_o);

    cp_trvk_cond: coverpoint {g_trvk_stage.cheri_trvk_stage_i.trvk_status,
                              g_trvk_stage.cheri_trvk_stage_i.cap_good_q[2],
                              g_trvk_stage.cheri_trvk_stage_i.range_ok_q[2]} iff
                             (g_trvk_stage.cheri_trvk_stage_i.rf_trvk_en_o) {
      wildcard ignore_bins ignore = {3'b?0?};   // if cap is not good, revocaton status/rang_ok are don't cares
    }

    cp_trvk_stall: coverpoint id_stage_i.stall_cheri_trvk;

    cp_trvk_stall_cause: coverpoint id_stage_i.id_stage_dv_ext_i.fcov_trvk_stall_cause iff 
                                     (id_stage_i.stall_cheri_trvk) {
      wildcard bins cs1hz  = {3'b??1};
      wildcard bins cs2hz  = {3'b?1?};
      wildcard bins cdhz  =  {3'b1??};
    }

    cp_rd_a_hz: coverpoint id_stage_i.gen_stall_mem.rf_rd_a_hz;
    cp_rd_b_hz: coverpoint id_stage_i.gen_stall_mem.rf_rd_b_hz;

    cp_tsmap_addr: coverpoint g_trvk_stage.cheri_trvk_stage_i.tsmap_addr_o iff
                             (g_trvk_stage.cheri_trvk_stage_i.tsmap_cs_o) {
       bins top     = {10'h3ff};
       bins middle  = {[10'h1:10'h3fe]};
       bins base    = {10'h0};
    }

    cp_tbre_fsm : coverpoint cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_sch_q {
      bins idle2load  = (0 => 1);
      bins idle2store = (0 => 2);
      bins load2idle  = (1 => 0);
      bins load2store = (1 => 2);
      bins store2idle = (2 => 0);
      bins store2load = (2 => 1);
    }
    
    // this equalss the tbre req fifo depth
    cp_tbre_os_cnt : coverpoint cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.os_req_cnt {
      bins normal[] = {[0:4]};
      illegal_bins illegal = default;
    } 

    cp_tbre_fifo_hazard : coverpoint {cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_dv_ext_i.fcov_tbre_fifo_hazard,
                                     cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_dv_ext_i.fcov_tbre_fifo_head_hazard} {
      wildcard bins bin1 = {2'b1?};
      wildcard bins bin2 = {2'b?1};
    }

    cp_tbre_mem_err: coverpoint cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_err_o;

    cp_concur_mem_reqs: coverpoint {g_cheri_ex.u_cheri_ex.lsu_req_o, 
                                   cheri_tbre_wrapper_i.g_tbre.cheri_tbre_i.tbre_lsu_req_o,
                                   cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_lsu_req_o};

    cp_tbrewrp_blk1_cancel: coverpoint  cheri_tbre_wrapper_i.tbre_wrapper_dv_ext_i.fcov_blk1_cancel;

    cp_stkz_sm: coverpoint cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_fsm_q {
      bins good[]      = {[0:2]};
      illegal_bins bad = default;
    }
   
    cp_stkz_ztop_wr: coverpoint cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_dv_ext_i.fcov_ztop_wr_type iff
                                (cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_dv_ext_i.ztop_wr_i);

    cp_stkz_mem_err: coverpoint cheri_tbre_wrapper_i.g_stkz.cheri_stkz_i.stkz_err_o;

    // mtcc and mepcc legalization 
    cp_mtcc_legalization_addr: coverpoint g_cheri_ex.u_cheri_ex.rf_rdata_a[1:0] iff
                              (cs_registers_i.mtvec_en_cheri) {
      bins good   = {2'h0}; 
      bins bad[]  = {[2'h1: 2'h3]};
    }

    cp_mtcc_legalization_perm: coverpoint cs_registers_i.cs_reg_dv_ext_i.fcov_scr_wfcap.perms[PERM_EX] iff
                                         (cs_registers_i.mtvec_en_cheri);

    cp_mtcc_legalization_sealed: coverpoint cs_registers_i.cs_reg_dv_ext_i.fcov_scr_wfcap.otype iff
                                            (cs_registers_i.mtvec_en_cheri) {
      bins good = {3'h0};
      bins bad  = {[3'h1:3'h7]};
    }

    cp_mepcc_legalization_addr: coverpoint g_cheri_ex.u_cheri_ex.rf_rdata_a[0] iff
                                          (cs_registers_i.mepc_en_cheri);

    cp_mepcc_legalization_perm: coverpoint cs_registers_i.cs_reg_dv_ext_i.fcov_scr_wfcap.perms[PERM_EX] iff
                                         (cs_registers_i.mepc_en_cheri);

    cp_mepcc_legalization_sealed: coverpoint cs_registers_i.cs_reg_dv_ext_i.fcov_scr_wfcap.otype iff
                                           (cs_registers_i.mepc_en_cheri) {
      bins good = {3'h0}; 
      bins bad  = {[3'h1:3'h7]};
    }

    // mret when PCC doesn't have PERM_SR
    cp_illegal_mret_cheri: coverpoint id_stage_i.controller_i.mret_cheri_asr_err;


    //pending fetch fault and interrupt
    cp_pending_vio_intr: coverpoint {id_stage_i.controller_i.handle_irq,if_stage_i.if_stage_dv_ext_i.fcov_pending_fetch_bound_vio};

    // 
    // Encoded coverage cases for address/bound checking
    //
    cp_cd_cs1_repr_cases: coverpoint  fcov_cd_cs1_repr_cases {
      bins case0 = {0};    
      bins case1 = {1};    
      bins case2 = {2};    
    }

    cp_cd_pcc_repr_cases: coverpoint  fcov_cd_pcc_repr_cases {
      bins case0 = {0};    
      bins case1 = {1};    
      bins case2 = {2};    
    }

    cp_cjal_target_bound_cases:  coverpoint fcov_cjal_target_bound_cases;
    cp_cjalr_target_bound_cases: coverpoint fcov_cjalr_target_bound_cases;
    cp_branch_target_bound_cases: coverpoint fcov_branch_target_bound_cases;

    cp_clsc_bound_cases: coverpoint fcov_clsc_bound_cases;
    cp_seal_bound_cases: coverpoint fcov_seal_bound_cases;

    cp_clsc_addr_lsb: coverpoint g_cheri_ex.u_cheri_ex.cheri_ls_chkaddr[2:0];

    cp_setbounds_cases: coverpoint fcov_setbounds_cases;
    cp_setboundsimm_cases: coverpoint fcov_setboundsimm_cases;
    cp_rs1_bitsize: coverpoint fcov_rs1_bitsize;

    cp_mstatus_mie: coverpoint cs_registers_i.csr_mstatus_mie_o;


    ///////////////////
    // Cross coverage
    ///////////////////

    misaligned_insn_bus_err_cross: cross id_stage_i.instr_fetch_err_i,
                                         id_stage_i.instr_fetch_err_plus2_i;

    // Include both mstatus.mie enabled/disabled because it should not affect wakeup condition
    irq_wfi_cross: cross cp_controller_fsm_sleep, cs_registers_i.mstatus_q.mie iff
                         (id_stage_i.irq_pending_i | id_stage_i.irq_nm_i);

    debug_wfi_cross: cross cp_controller_fsm_sleep, cp_all_debug_req iff
                           (id_stage_i.controller_i.controller_dv_ext_i.fcov_all_debug_req);

    priv_mode_instr_cross: cross cp_priv_mode_id, cp_id_instr_category {
      // No un-privileged CSRs on Ibex so no InstrCategoryCSRAccess in U mode (any CSR instruction
      // becomes InstrCategoryCSRIllegal).
      illegal_bins umode_csr_access_illegal =
        binsof(cp_id_instr_category) intersect {InstrCategoryCSRAccess} &&
        binsof(cp_priv_mode_id) intersect {PRIV_LVL_U};
    }

    priv_mode_irq_cross: cross cp_priv_mode_id, cp_interrupt_taken, cs_registers_i.mstatus_q.mie {
      // No interrupt would be taken in M-mode when its mstatus.MIE = 0 unless it's an NMI
      illegal_bins mmode_mstatus_mie =
        binsof(cs_registers_i.mstatus_q.mie) intersect {1'b0} &&
        binsof(cp_priv_mode_id) intersect {PRIV_LVL_M} with (cp_interrupt_taken >> 4 == 6'd0);
    }

    // priv_mode_exception_cross: cross cp_priv_mode_id, cp_ls_pmp_exception, cp_ls_error_exception {
    priv_mode_exception_cross: cross cp_priv_mode_id, cp_ls_exception;
    // {
    //  illegal_bins pmp_and_error_exeption_both =
    //    (binsof(cp_ls_pmp_exception) intersect {1'b1} &&
    //     binsof(cp_ls_error_exception) intersect {1'b1});
    //}

    `define ListOfInstrRegOperands  {InstrCategoryALU, InstrCategoryMul, \ 
                                     InstrCategoryDiv, InstrCategoryBranch, \
                                     InstrCategoryCJAL, InstrCategoryCJALR, \
                                     InstrCategoryLoad, InstrCategoryStore, \
                                     InstrCategoryCSRAccess, \
                                     InstrCategoryCheriQuery, InstrCategoryCheriSCR, \
                                     InstrCategoryCheriMod, \
                                     InstrCategoryCheriAddr, InstrCategoryCheriBounds, \
                                     InstrCategoryCheriCLC, InstrCategoryCheriCSC}

    stall_cross: cross cp_id_instr_category, cp_stall_type_id {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryCJAL, InstrCategoryCJALR} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeInstr})
    ||
        // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSR Access can see a load hazard stall
        (!binsof(cp_id_instr_category) intersect `ListOfInstrRegOperands &&
         binsof(cp_stall_type_id) intersect {IdStallTypeLdHz, IdStallTypeTRVK});
    }

    wb_reg_no_load_hz_instr_cross: cross cp_id_instr_category, cp_wb_reg_no_load_hz {
      // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSRAccess instructions can see a WB
      // register hazard
      illegal_bins illegal =
        !binsof(cp_id_instr_category) intersect `ListOfInstrRegOperands &&
        binsof(cp_wb_reg_no_load_hz) intersect {1'b1};
    }

    pipe_cross: cross cp_id_instr_category, cp_if_stage_state, cp_id_stage_state, cp_wb_stage_state {
      // QQQ IF stage shouldn't be idle unless when sleep or reset 
      // ignore_bins ignore = (!binsof(cp_id_instr_category) intersect {InstrCategoryWFI, InstrCategoryNone} &&
      ignore_bins ignore0 = ( binsof(cp_if_stage_state) intersect {IFStageEmptyAndIdle, IFStageFullAndIdle});
      // When ID stage is empty the only legal instruction category is InstrCategoryNone. Conversly
      // when the instruction category is InstrCategoryNone the only legal ID stage state is
      // PipeStageEmpty.
      illegal_bins illegal0 = (!binsof(cp_id_instr_category) intersect {InstrCategoryNone} &&
        binsof(cp_id_stage_state) intersect {PipeStageEmpty}) ||
      (binsof(cp_id_instr_category) intersect {InstrCategoryNone} &&
        !binsof(cp_id_stage_state) intersect {PipeStageEmpty}); 
      // Impossible to have a case where WB is stalled but ID is not
      illegal_bins illegal1 = (binsof(cp_id_stage_state) intersect {PipeStageFullAndUnstalled}) &&
                              (binsof(cp_wb_stage_state) intersect {PipeStageFullAndStalled}); 
    }

    // interrupt_taken_instr_cross: cross cp_nmi_taken, instr_unstalled_last,
    interrupt_taken_instr_cross: cross cp_interrupt_taken, instr_unstalled_last,
      cp_id_instr_category_last iff (id_stage_i.controller_i.fcov_interrupt_taken);

    debug_instruction_cross: cross cp_debug_mode, cp_id_instr_category;

    debug_entry_if_instr_cross: cross cp_debug_entry_if, instr_unstalled_last,
      cp_id_instr_category_last;
    pipe_flush_instr_cross: cross cp_pipe_flush, instr_unstalled, cp_id_instr_category;

    // exception_stall_instr_cross: cross cp_ls_pmp_exception, cp_ls_error_exception, cp_ls_cheri_exception,
    exception_stall_instr_cross: cross cp_ls_exception,
      // cp_id_instr_category, cp_stall_type_id, instr_unstalled, cp_irq_pending, cp_debug_req {  // QQQ add cp_debug_req back later
      cp_id_instr_category, cp_stall_type_id, instr_unstalled, cp_irq_pending {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryCJAL, InstrCategoryCJALR} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeInstr})
    ||
        // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSR Access can see a load hazard stall
        (!binsof(cp_id_instr_category) intersect `ListOfInstrRegOperands && 
         binsof(cp_stall_type_id) intersect {IdStallTypeLdHz});

      // Cannot have a memory stall when we see an LS exception unless it is a load or store
      // instruction
      //  InstrCategoryFetchError can still see mem_stall (since decoder generates lsu_dec in this case)
      illegal_bins mem_stall_illegal =
        (!binsof(cp_id_instr_category) intersect {InstrCategoryLoad, InstrCategoryStore, InstrCategoryCheriCLC, InstrCategoryCheriCSC,  InstrCategoryFetchError} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeMem}) with
        (cp_ls_exception == 2'h2 || cp_ls_exception == 2'h3);

      // When pipeline has unstalled stall type will always be none
      illegal_bins unstalled_illegal =
        !binsof(cp_stall_type_id) intersect {IdStallTypeNone} with (instr_unstalled == 1'b1);
    }

    csr_read_only_priv_cross: cross cp_csr_read_only, cp_priv_mode_id;
    csr_write_priv_cross: cross cp_csr_write, cp_priv_mode_id;

    csr_read_only_debug_cross: cross cp_csr_read_only, cp_debug_mode {
      // Only care about specific debug CSRs
      ignore_bins ignore = !binsof(cp_csr_read_only) intersect {`DEBUG_CSRS};
    }

    csr_write_debug_cross: cross cp_csr_write, cp_debug_mode {
      // Only care about specific debug CSRs
      ignore_bins ignore = !binsof(cp_csr_write) intersect {`DEBUG_CSRS};
    }

    // V2S Crosses

    dummy_instr_config_cross: cross cp_dummy_instr_type, cp_dummy_instr_mask
                                iff (cs_registers_i.dummy_instr_en_o);

    rf_ecc_err_cross: cross ibex_core_dv_ext_i.fcov_rf_ecc_err_a_id, 
                            ibex_core_dv_ext_i.fcov_rf_ecc_err_b_id
                                iff (id_stage_i.instr_valid_i);

    // Each stage sees a debug request while executing a dummy instruction.
    debug_req_dummy_instr_if_stage_cross: cross cp_debug_req, cp_dummy_instr_if_stage;
    debug_req_dummy_instr_id_stage_cross: cross cp_debug_req, cp_dummy_instr_id_stage;
    //debug_req_dummy_instr_wb_stage_cross: cross cp_debug_req, cp_dummy_instr_wb_stage;

    // Each stage sees an interrupt request while executing a dummy instruction.
    irq_pending_dummy_instr_if_stage_cross: cross cp_irq_pending, cp_dummy_instr_if_stage;
    irq_pending_dummy_instr_id_stage_cross: cross cp_irq_pending, cp_dummy_instr_id_stage;
    //irq_pending_dummy_instr_wb_stage_cross: cross cp_irq_pending, cp_dummy_instr_wb_stage;

    //
    // CHERIoT cross coverage
    //
    
    // cs1/cs2/cd cross. QQQ need to further cross with instr types.
    rs_rd_cross: cross cp_rs1_regaddr, cp_rs2_regaddr, cp_rd_regaddr;
   
    // Cap manipulation and tag clearing
    //  QQQ CAUIPCC/CJAL/CJALR needs to be treated separately since it's from PCC, not cs1
    `define ListOfCs1CdInstr {CSEAL, CUNSEAL, CSET_ADDR, CINC_ADDR, \
                              CINC_ADDR_IMM, CSET_BOUNDS, CSET_BOUNDS_EX, \
                              CSET_BOUNDS_IMM, CAUICGP, CSEAL, CUNSEAL}
    `define ListOfPcc2CdInstr {CAUIPCC, CJAL, CJALR}

    cheri_cs1cd_tag_cross: cross cp_cs1_tag, cp_cd_tag, cp_cheri_instr_set {
      ignore_bins ignore0 = 
        ((!binsof(cp_cheri_instr_set) intersect `ListOfCs1CdInstr) ||
        ((binsof(cp_cs1_tag) intersect {1'b0}) && (binsof(cp_cd_tag) intersect {1'b0}))); 
      illegal_bins illegal = 
        ((binsof(cp_cs1_tag) intersect {1'b0}) && (binsof(cp_cd_tag) intersect {1'b1}) &&
         (binsof(cp_cheri_instr_set) intersect `ListOfCs1CdInstr));
    }

    cheri_pcc2cd_tag_cross: cross cp_pcc_tag, cp_cd_tag, cp_cheri_instr_set {
      ignore_bins ignore0 = 
        ((!binsof(cp_cheri_instr_set) intersect `ListOfPcc2CdInstr) ||
        ((binsof(cp_pcc_tag) intersect {1'b0}))); 
      illegal_bins illegal = 
        ((binsof(cp_pcc_tag) intersect {1'b0}) && (binsof(cp_cd_tag) intersect {1'b1}) &&
         (binsof(cp_cheri_instr_set) intersect `ListOfPcc2CdInstr)) ||
        ((binsof(cp_pcc_tag) intersect {1'b1}) && (binsof(cp_cd_tag) intersect {1'b0}) &&
         (binsof(cp_cheri_instr_set) intersect {CJAL, CJALR}));
    }

    cheri_xfer_room_cross: cross cp_lsu_xfer_size, cp_ls_room_cs1_chk;
    
    // non-load/store CHERI exceptions
    cheri_jump_exception_cross: cross cp_cheri_wb_exception_causes, cp_cheri_instr_set {
      ignore_bins ignore0 = 
        (!binsof(cp_cheri_instr_set) intersect {CJALR});  // only CJALR generate exceptions now..
      illegal_bins illegal1 = 
        ((binsof(cp_cheri_instr_set) intersect {CJALR}) && (binsof(cp_cheri_wb_exception_causes) intersect {5'h0, 5'h1, 5'h18}));  
    }
    
    cheri_scr_exception_cross: cross cp_cheri_wb_exception_causes, cp_cheri_instr_set {
      ignore_bins ignore0 = 
        (!binsof(cp_cheri_instr_set) intersect {CCSR_RW}) ||
        (!binsof(cp_cheri_wb_exception_causes.perm_sr));
    }
    
    // LSU access cross QQQ
    cheri_clc_clrperm_cross: cross cp_clc_clrperm, cp_clc_mem_cap_perms;

    // IF fetch violation
    cheri_fetch_cross: cross cp_cheri_fetch_tag_vio, cp_cheri_fetch_bound_vio;

    // trvk stall 
    cheri_trvk_cross: cross cp_trvk_stall, cp_rd_a_hz, cp_rd_b_hz;

    // stkz ztop writes
    cheri_stkz_wr_cross: cross cp_stkz_sm, cp_stkz_ztop_wr {
       ignore_bins igore0 = (binsof(cp_stkz_sm) intersect {2'b10});   // ABORT state
    }

    // Instruction/error/interrupt sequence coverage
    // -- note instructions faulted at ID stage doesn't go to WB stage, so we need both cross items below
    instr_error_sequence_cross0: cross id_instr_category, wb_instr_category, id_stage_i.controller_i.handle_irq, fcov_id_error, fcov_wb_err;
    instr_error_sequence_cross1: cross id_instr_category, id_instr_category_q, fcov_id_exc_int, fcov_id_exc_int_q;


    /////////////////////////////////////////////
    // CHERIoT instruction (cross) coverage
    /////////////////////////////////////////////

    //
    // Capability address computation instructions
    //

    // AUICGP
    cp_instr_auicgp: coverpoint cheri_ops[CAUICGP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_auicgp_cross: cross cp_cs1_tag, cp_cd_cs1_repr_cases, cp_cs1_sealed, cp_cs1_exp, cp_cheri_imm20, cp_instr_auicgp; 

    // AUIPCC
    cp_instr_auipcc: coverpoint cheri_ops[CAUIPCC]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_auipcc_cross: cross cp_cd_pcc_repr_cases, cp_pcc_exp, cp_cheri_imm20, cp_instr_auipcc; 

    // CINCADDRIMM
    cp_instr_cincaddrimm: coverpoint cheri_ops[CINC_ADDR_IMM]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cincaddrimm_cross: cross cp_cs1_tag, cp_cd_cs1_repr_cases, cp_cs1_sealed, cp_cs1_exp, cp_cheri_imm12, cp_instr_cincaddrimm; 
    // CINCADDR
    cp_instr_cincaddr: coverpoint cheri_ops[CINC_ADDR]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cincaddr_cross: cross cp_cs1_tag, cp_cd_cs1_repr_cases, cp_cs1_sealed, cp_cs1_exp, cp_rs2_as_inc, cp_instr_cincaddr;
 
    // CSETADDR
    cp_instr_csetaddr: coverpoint cheri_ops[CSET_ADDR]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_csetaddr_cross: cross cp_cs1_tag, cp_cd_cs1_repr_cases, cp_cs1_sealed, cp_cs1_exp, cp_instr_csetaddr; 

    //
    // Capbility mod/simple arithmetic instructions
    //

    // CANDPERM
    cp_instr_candperm: coverpoint cheri_ops[CAND_PERM]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_candperm_cross: cross cp_cs1_tag, cp_cs1_sealed, cp_cs1_perms, cp_rs2_perm_mask, cp_instr_csetaddr; 

    // CCLEARTAG
    cp_instr_ccleartag: coverpoint cheri_ops[CCLEAR_TAG]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_ccleartag_cross: cross cp_cs1_tag, cp_cs1_sealed, cp_instr_ccleartag; 

    // CMOVE
    cp_instr_cmove: coverpoint cheri_ops[CMOVE_CAP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cmove_cross: cross cp_cs1_tag, cp_cs1_sealed, cp_instr_cmove; 

    // CSEQX
    cp_instr_cseqx: coverpoint cheri_ops[CIS_EQUAL]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_cseqx_cross0: cross cp_cs1_tag, cp_cs1_otype, cp_cs2_tag, cp_cs2_otype, cp_instr_cseqx; 
    cheriot_instr_cseqx_cross1: cross cp_cs1_perms, cp_cs1_cor, cp_cs2_perms, cp_cs2_cor, cp_instr_cseqx; 
    cheriot_instr_cseqx_cross2: cross cp_cs1_top, cp_cs1_base, cp_cs2_top, cp_cs2_base, cp_instr_cseqx; 
    cheriot_instr_cseqx_cross3: cross cp_cs1_address, cp_cs2_address, cp_instr_cseqx; 
   
    // CTESTSUBSET
    cp_instr_ctestsubset: coverpoint cheri_ops[CIS_SUBSET]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_ctestsubset_cross0: cross cp_cs1_tag, cp_cs1_otype, cp_cs2_tag, cp_cs2_otype, cp_instr_ctestsubset; 
    cheriot_instr_ctestsubset_cross1: cross cp_cs1_perms, cp_cs1_cor, cp_cs2_perms, cp_cs2_cor, cp_instr_ctestsubset; 
    cheriot_instr_ctestsubset_cross2: cross cp_cs1_top, cp_cs1_base, cp_cs2_top, cp_cs2_base, cp_instr_ctestsubset; 
   
    // CSUB
    cp_instr_csub: coverpoint cheri_ops[CSUB_CAP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csub_cross: cross cp_cs1_tag, cp_cs1_address, cp_cs2_tag,  cp_cs2_address, cp_instr_csub; 

    // CSETHIGH
    cp_instr_csethigh: coverpoint cheri_ops[CSET_HIGH]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csethigh_cross0: cross cp_cd_tag, cp_cd_otype, cp_cd_cperms, cp_instr_csethigh; 
    cheriot_instr_csethigh_cross1: cross cp_cd_cor, cp_cd_exp, cp_cd_top, cp_cd_base, cp_cd_address, cp_instr_csethigh; 
    
    //
    // Capbility query (cget*) instructions
    //

    // CGETADDR
    cp_instr_cgetaddr: coverpoint cheri_ops[CGET_ADDR]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgetaddr_cross: cross cp_cs1_tag, cp_cs1_address, cp_instr_cgetaddr; 

    // CGETBASE
    cp_instr_cgetbase: coverpoint cheri_ops[CGET_BASE]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgetbase_cross: cross cp_cs1_tag, cp_cs1_base32, cp_instr_cgetbase; 

    // CGETTOP
    cp_instr_cgettop: coverpoint cheri_ops[CGET_TOP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgettop_cross: cross cp_cs1_tag, cp_cs1_top33, cp_instr_cgettop; 

    // CGETTYPE
    cp_instr_cgettype: coverpoint cheri_ops[CGET_TYPE]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgettype_cross: cross cp_cs1_tag, cp_cs1_otype, cp_instr_cgettype; 

    // CGETPERM
    cp_instr_cgetperm: coverpoint cheri_ops[CGET_PERM]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgetperm_cross: cross cp_cs1_tag, cp_cs1_perms, cp_instr_cgetperm; 

    // CGETTAG
    cp_instr_cgettag: coverpoint cheri_ops[CGET_TAG]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgettag_cross: cross cp_cs1_tag, cp_instr_cgettag; 

    // CGETLEN
    cp_instr_cgetlen: coverpoint cheri_ops[CGET_LEN]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgetlen_cross: cross cp_cs1_tag, cp_cs1_top33, cp_cs1_base32, cp_cs1_exp, cp_instr_cgetlen; 

    // CGETHIGH
    cp_instr_cgethigh: coverpoint cheri_ops[CGET_HIGH]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cgethigh_cross0: cross cp_cs1_tag, cp_cs1_otype, cp_cs1_perms, cp_instr_cgethigh; 
    cheriot_instr_cgethigh_cross1: cross cp_cs1_cor, cp_cs1_exp, cp_cs1_top, cp_cs1_base, cp_cs1_address, cp_instr_cgethigh; 

    //
    // Cspecialrw instruction
    //
    //
    cp_instr_cspecialrw: coverpoint cheri_ops[CCSR_RW]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cspecialrw_cross: cross cp_scr_addr, cp_rs1_regaddr, cp_rd_regaddr, cp_pcc_perm_asr, cp_instr_cspecialrw; 

  
    //
    // Jump and branch instructions
    //

    // CJAL
    cp_instr_cjal: coverpoint cheri_ops[CJAL]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_cjal_cross: cross cp_rd_regaddr, cp_cjal_target_bound_cases, cp_cheri_imm20, cp_mstatus_mie, cp_instr_cjal; 

    // CJALR
    cp_instr_cjalr: coverpoint cheri_ops[CJALR]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    //  -- imm12 is part of seal violation evaluation
    cheriot_instr_cjalr_cross0: cross cp_cs1_tag, cp_cs1_otype, cp_rd_regaddr, cp_mstatus_mie, cp_cheri_imm12, cp_instr_cjalr; 
    cheriot_instr_cjalr_cross1: cross cp_cs1_tag, cp_cs1_perm_ex, cp_cjalr_target_bound_cases, cp_cheri_imm12, cp_instr_cjalr; 

    // Branch
    cp_instr_branch: coverpoint ((id_stage_i.instr_rdata_i[6:0] == OPCODE_BRANCH) & id_stage_i.branch_decision_i) iff 
                    (id_stage_i.instr_executing) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_branch_cross: cross cp_branch_target_bound_cases, cp_instr_branch; 

    //
    // Load and store instructions
    //

    // CLC
    cp_instr_clc: coverpoint cheri_ops[CLOAD_CAP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_clc_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_cs1_perms_load, cp_clc_mem_cap_perms, cp_instr_clc; 
    cheriot_instr_clc_cross1: cross cp_cs1_tag, cp_clsc_bound_cases, cp_cheri_imm12, cp_clsc_addr_lsb, cp_instr_clc; 
    
    // CSC
    cp_instr_csc: coverpoint cheri_ops[CSTORE_CAP]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csc_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_cs1_perms_store, cp_cs2_perm_gl, cp_instr_csc; 
    cheriot_instr_csc_cross1: cross cp_cs1_tag, cp_clsc_bound_cases, cp_cheri_imm12, cp_clsc_addr_lsb, cp_instr_csc; 

    //
    // Seal/unseal  instructions
    //

    // CSeal
    cp_instr_cseal: coverpoint cheri_ops[CSEAL]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_cseal_cross0: cross cp_cs1_tag, cp_cs1_sealed,  cp_cs2_tag, cp_cs2_sealed, cp_instr_cseal; 
    cheriot_instr_cseal_cross1: cross cp_cs1_perm_ex, cp_cs2_tag, cp_cs2_perm_se, cp_cs2_seal_type, cp_seal_bound_cases, cp_instr_cseal; 
    
    // CUnseal
    cp_instr_cunseal: coverpoint cheri_ops[CUNSEAL]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_cunseal_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_cs1_perm_gl, 
                                        cp_cs2_tag, cp_cs2_sealed, cp_cs2_perm_us, cp_cs2_perm_gl, cp_instr_cunseal; 
    cheriot_instr_cunseal_cross1: cross cp_cs1_otype, cp_cs1_perm_ex, 
                                        cp_cs2_tag, cp_cs2_seal_type, cp_seal_bound_cases, cp_instr_cunseal; 
    //
    // Set_bounds instructions
    //

    // CSetbounds
    cp_instr_csetbounds: coverpoint cheri_ops[CSET_BOUNDS]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csetbounds_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_setbounds_cases, cp_cs1_base32, cp_cs1_top33, cp_cs1_exp, 
                                           cp_cd_tag, cp_instr_csetbounds; 
   
    // CSetboundsexact
    cp_instr_csetboundsexact: coverpoint cheri_ops[CSET_BOUNDS_EX]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csetboundsexact_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_setbounds_cases, cp_cs1_base32, cp_cs1_top33, cp_cs1_exp, 
                                                cp_cd_tag, cp_instr_csetboundsexact; 
   
    // CSetboundsimm
    cp_instr_csetboundsimm: coverpoint cheri_ops[CSET_BOUNDS_IMM]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_csetboundsimm_cross0: cross cp_cs1_tag, cp_cs1_sealed, cp_setboundsimm_cases, cp_cs1_base32, cp_cs1_top33, cp_cs1_exp, 
                                                cp_cd_tag, cp_instr_csetboundsimm; 
   
    // CRAM
    cp_instr_cram: coverpoint cheri_ops[CRAM]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }

    cheriot_instr_cram_cross: cross cp_cs1_tag, cp_rs1_bitsize, cp_instr_cram; 

    // CRRL
    cp_instr_crrl: coverpoint cheri_ops[CRRL]  iff (g_cheri_ex.u_cheri_ex.cheri_exec_id_i) {
      bins bin1 = {1'b1};
    }
    
    cheriot_instr_crrl_cross: cross cp_cs1_tag, cp_rs1_bitsize, cp_instr_crrl;
 
  endgroup

  bit en_uarch_cov;

  initial begin
   void'($value$plusargs("enable_ibex_fcov=%d", en_uarch_cov));
   $display("enable_ibex_fcov = %d", en_uarch_cov);
  end

  `DV_FCOV_INSTANTIATE_CG(uarch_cg, en_uarch_cov)
endinterface
