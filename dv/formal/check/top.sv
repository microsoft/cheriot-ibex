// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This is the top module. Everything else in check will be included into this file.
This module contains the ibex instance, the specification instance and the assertions
(included via the built psgen file).

It has the same ports as the ibex top.
*/

// Preprocessor decoding of instructions
`include "encodings.sv"

`define CR ibex_top_i.u_ibex_core
`define CSR `CR.cs_registers_i
`define CSRG `CSR.gen_scr
`define CSRP `CSR.g_pmp_registers
`define LSU `CR.load_store_unit_i
`define ID `CR.id_stage_i
`define IDG `ID.gen_stall_mem
`define IDC `ID.controller_i
`define WB `CR.wb_stage_i
`define WBG `WB.g_writeback_stage
`define RF ibex_top_i.gen_regfile_cheriot.register_file_i
`define IF `CR.if_stage_i
`define IFP `IF.gen_prefetch_buffer.prefetch_buffer_i
`define IFF `IFP.fifo_i
`define MULT `CR.ex_block_i.gen_multdiv_fast.multdiv_i
`define MULTG `MULT.gen_mult_fast
`define CE `CR.g_cheri_ex.u_cheri_ex
`define TRVK `CR.g_trvk_stage.cheri_trvk_stage_i

module top import ibex_pkg::*; #(
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  parameter bit          SecureIbex       = 1'b0,
  parameter bit          WritebackStage   = 1'b1,
  parameter bit          RV32E            = 1'b1,
  parameter int unsigned PMPNumRegions    = 4,
  parameter int unsigned HeapBase         = 32'h2001_0000,
  parameter int unsigned TSMapSize        = 1024           // 32-bit words
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         test_en_i,     // enable all clock gates for testing
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input  logic                         cheri_pmode_i,
  input  logic                         cheri_tsafe_en_i,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [31:0]                  instr_rdata_i,
  input  logic [6:0]                   instr_rdata_intg_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  output logic                         data_is_cap_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [32:0]                  data_wdata_o,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [32:0]                  data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  // TS map memory interface
  output logic                         tsmap_cs_o,
  output logic [15:0]                  tsmap_addr_o,
  input  logic [31:0]                  tsmap_rdata_i,
  input  logic [6:0]                   tsmap_rdata_intg_i,
  input  logic [127:0]                 mmreg_corein_i,
  output logic [63:0]                  mmreg_coreout_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt

  // Scrambling Interface
  input  logic                         scramble_key_valid_i,
  input  logic [SCRAMBLE_KEY_W-1:0]    scramble_key_i,
  input  logic [SCRAMBLE_NONCE_W-1:0]  scramble_nonce_i,
  output logic                         scramble_req_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  output logic                         double_fault_seen_o,

  // CPU Control Signals
  input  fetch_enable_t                fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         core_sleep_o,

  // DFT bypass controls
  input logic                          scan_rst_ni
);

default clocking @(posedge clk_i); endclocking

ibex_top #(
    .DmHaltAddr(DmHaltAddr),
    .DmExceptionAddr(DmExceptionAddr),
    .SecureIbex(SecureIbex),
    .WritebackStage(WritebackStage),
    .RV32E(RV32E),
    .CheriTBRE(1'b1), // Include it, but don't let it run (see assumption 6 below)
    .CheriStkZ(1'b0),
    .BranchTargetALU(1'b1),
    .TSMapSize(TSMapSize),
    .HeapBase(HeapBase)
) ibex_top_i(.*);

// Core constraints
// 1. We do not allow going into debug mode
NotDebug: assume property (!ibex_top_i.u_ibex_core.debug_mode & !debug_req_i & !`CSR.csr_dbg_tclr_fault_o);
// 2. The boot address is constant
ConstantBoot: assume property (boot_addr_i == $past(boot_addr_i));
// 3. Always fetch enable
FetchEnable: assume property (fetch_enable_i == IbexMuBiOn);
// 4. CHERI pure mode enable, with temporal safety
CheriConfig: assume property (cheri_pmode_i & cheri_tsafe_en_i);
// 5. Never start doing TBRE
TBRENoGo: assume property (~mmreg_corein_i[64]); // This is tbre_ctrl.go

// See protocol/* for further assumptions

///////////////////////////////// Declarations /////////////////////////////////

// Helpful macros to define each CSR and their types

// Note: does not include mcycle, since it's not that meaningful to check it
`define X_EACH_CSR_C \
    `X(pcc) \
    `X(mtvec) \
    `X(mtdc) \
    `X(mscratchc) \
    `X(mepc)

`define X_EACH_CSR_NC \
    `ifndef X_DISABLE_PC `X(pc) `endif \
    `X(priv) \
    `X(mstatus) \
    `X(mie) \
    `X(mcause) \
    `X(mtval) \
    `X(mscratch) \
    `X(mcounteren) \
    `X(nmi_mode) \
    `X(mstack) \
    `X(mstack_epc) \
    `X(mstack_cause)

    // `X(mshwmb) \
    // `X(mshwm)

`define X_EACH_CSR `X_EACH_CSR_C `X_EACH_CSR_NC

`define X_EACH_CSR_TYPED \
    logic [31:0] `X(pc); \
    t_Privilege `X(priv); \
    mstatus_t `X(mstatus); \
    logic [31:0] `X(mie); \
    logic [31:0] `X(mcause); \
    t_Capability `X(pcc); \
    logic [31:0] `X(mtval); \
    t_Capability `X(mtvec); \
    logic [31:0] `X(mscratch); \
    t_Capability `X(mepc); \
    t_Capability `X(mscratchc); \
    t_Capability `X(mtdc); \
    logic [63:0] `X(mcycle); \
    logic [31:0] `X(mcounteren); \
    logic `X(nmi_mode); \
    mstatus_t `X(mstack); \
    logic [31:0] `X(mstack_epc); \
    logic [31:0] `X(mstack_cause);
    
    // logic [31:0] `X(mshwmb); \
    // logic [31:0] `X(mshwm); \

////////////////////// Abstract State //////////////////////
logic [31:0] pcc_address_d, pcc_address_q;

t_Capability pre_regs[31:0];
t_Capability pre_regs_cut[31:1]; // This is the direct input to the spec, it contains only at most 2 registers
logic [31:0] pre_nextpc;
logic [31:0] pre_mip;

`define X(n) pre_``n
`X_EACH_CSR_TYPED
`undef X

`define X(n) post_``n
`X_EACH_CSR_TYPED
`undef X
t_Capability post_trvk_regs[15:0];

////////////////////// Following //////////////////////

logic ex_is_wfi, ex_is_rtype, ex_is_div;
logic ex_is_btype, ex_is_jump;
logic ex_is_mem_cap_instr;
logic ex_is_mem_instr, ex_is_load_instr, ex_is_store_instr;
logic ex_has_branched_d, ex_has_branched_q;
logic ex_is_clc;
logic [31:0] ex_branch_dst;
assign ex_branch_dst = `CR.branch_decision ? `CR.branch_target_ex : pre_nextpc;

logic outstanding_mem;
assign outstanding_mem = `ID.outstanding_load_wb_i || `ID.outstanding_store_wb_i;

logic has_resp_waiting_q, has_resp_waiting_d;
assign has_resp_waiting_q = data_mem_assume.outstanding_reqs_q != 8'h0;
assign has_resp_waiting_d = data_mem_assume.outstanding_reqs != 8'h0;

logic has_one_resp_waiting_q, has_one_resp_waiting_d;
assign has_one_resp_waiting_q = data_mem_assume.outstanding_reqs_q == 8'h1;
assign has_one_resp_waiting_d = data_mem_assume.outstanding_reqs == 8'h1;

logic has_two_resp_waiting_q, has_two_resp_waiting_d;
assign has_two_resp_waiting_q = data_mem_assume.outstanding_reqs_q == 8'h2;
assign has_two_resp_waiting_d = data_mem_assume.outstanding_reqs == 8'h2;

logic wbexc_is_load_instr, wbexc_is_store_instr;
logic wbexc_is_mem_instr;
logic wbexc_is_mem_cap_instr;

logic [31:0] idex_compressed_instr;
logic idex_has_compressed_instr;

logic wbexc_post_int_err;
t_Capability wbexc_post_wX;
logic [5:0] wbexc_post_wX_addr;
logic wbexc_post_wX_en;

`define X(n) wbexc_post_``n
`X_EACH_CSR_TYPED
`undef X

logic [31:0] wbexc_spec_mem_read_fst_rdata;
logic [31:0] wbexc_spec_mem_read_snd_rdata;
logic wbexc_spec_mem_read_tag;

t_Capability wbexc_spec_mem_read_cap;
assign wbexc_spec_mem_read_cap = capBitsToCapability(wbexc_spec_mem_read_tag, {wbexc_spec_mem_read_snd_rdata, wbexc_spec_mem_read_fst_rdata});
CapBoundBits wbexc_spec_mem_read_cap_bounds;
assign wbexc_spec_mem_read_cap_bounds = getCapBoundsBitsRaw(
    wbexc_spec_mem_read_cap.E,
    wbexc_spec_mem_read_cap.B,
    wbexc_spec_mem_read_cap.T,
    wbexc_spec_mem_read_cap.address
);

logic wbexc_spec_mem_revoke_en;
logic[31:0] wbexc_spec_mem_revoke_addr;
logic wbexc_spec_mem_revoke;


`define X(n) wbexc_dut_post_``n
`X_EACH_CSR_TYPED
`undef X

logic [31:0] wbexc_instr; // original potentially compressed
logic [31:0] wbexc_decompressed_instr; // post decompression
logic wbexc_is_compressed;

logic [31:0] wbexc_pc;

logic mem_gnt_fst_d; // We are having or have had the first gnt
logic mem_gnt_fst_q; // We have had the first gnt before now
logic mem_gnt_snd_d; // We are having or have had the second gnt
logic mem_gnt_snd_q; // We have had the second gnt before now

logic mem_req_fst_d; // We are having the first req
logic mem_req_snd_d; // We are having the second req

logic mem_resp_d; // We are having for have had an rvalid for EX
logic mem_resp_q; // We have had an rvalid for EX

logic wbexc_mem_had_snd_req; // During ID/EX there was a second request

logic lsu_had_first_resp;
assign lsu_had_first_resp = (`LSU.ls_fsm_cs == `LSU.WAIT_GNT && `LSU.split_misaligned_access) || (`LSU.lsu_is_cap_i && `LSU.cap_rx_fsm_q == CRX_WAIT_RESP2);

////////////////////// Wrap signals //////////////////////

logic spec_en;
logic has_spec_past;

t_Capability spec_past_regs[31:0];
logic [31:0] spec_past_has_reg;
`define X(n) spec_past_``n
`X_EACH_CSR_TYPED
`undef X

////////////////////// Pipeline signals //////////////////////

logic ex_success; // Execute stage succeeding
logic ex_err; // Execute stage erroring
logic ex_kill; // Execute stage killed
logic exc_finishing; // Exception finishing
logic wb_finishing; // WB finishing
logic wbexc_finishing; // WB/EXC finishing
logic wbexc_exists; // Instruction in WB/EXC
logic wbexc_ex_err; // EXC has an execute error
logic wbexc_fetch_err; // EXC has a fetch error
logic wbexc_illegal; // EXC has an illegal instruction
logic wbexc_compressed_illegal; // EXC has an illegal instruction
logic wbexc_err; // EXC has an error
logic instr_will_progress; // Instruction will finish EX
logic wbexc_is_wfi;
logic wfi_will_finish;
logic wbexc_has_prev; // The next instruction should start with the state given
logic wbexc_csr_pipe_flush;
logic wbexc_handling_irq;

////////////////////// CSR selection //////////////////////

// WBEXC CSR dut post state
`define X(n) wbexc_dut_cmp_post_``n
`X_EACH_CSR_TYPED
`undef X

// WBEXC CSR spec post state
`define X(n) wbexc_spec_cmp_post_``n
`X_EACH_CSR_TYPED
`undef X

////////////////////// Spec Post //////////////////////

t_Capability spec_post_wX;
logic [4:0] spec_post_wX_addr;
logic spec_post_wX_en;

`define X(n) spec_post_``n
`X_EACH_CSR_TYPED
`undef X

logic spec_int_err;
t_MainMode main_mode;

logic spec_fetch_err;
assign spec_fetch_err =
    (main_mode == MAIN_IFERR && spec_api_i.main_result == MAINRES_OK) ||
    spec_api_i.main_result == MAINRES_IFERR_1 || spec_api_i.main_result == MAINRES_IFERR_2;

logic spec_mem_read;
logic spec_mem_read_snd;
logic [31:0] spec_mem_read_fst_addr;
logic [31:0] spec_mem_read_snd_addr;
logic [31:0] spec_mem_read_fst_rdata; // Undriven
logic [31:0] spec_mem_read_snd_rdata; // Undriven
logic spec_mem_read_tag; // Undriven

t_Capability spec_mem_read_cap;
assign spec_mem_read_cap = capBitsToCapability(spec_mem_read_tag, {spec_mem_read_snd_rdata, spec_mem_read_fst_rdata});

logic spec_mem_revoke_en;
logic[31:0] spec_mem_revoke_addr;
logic spec_mem_revoke; // Undriven

logic spec_mem_write;
logic spec_mem_write_snd;
logic [31:0] spec_mem_write_fst_addr;
logic [31:0] spec_mem_write_snd_addr;
logic [31:0] spec_mem_write_fst_wdata;
logic [31:0] spec_mem_write_snd_wdata;
logic [3:0] spec_mem_write_fst_be;
logic [3:0] spec_mem_write_snd_be;
logic spec_mem_write_tag;

logic spec_mem_en;
logic spec_mem_en_snd;
logic [31:0] spec_mem_fst_addr;
logic [31:0] spec_mem_snd_addr;

assign spec_mem_en = spec_mem_read | spec_mem_write;
assign spec_mem_en_snd = spec_mem_read_snd | spec_mem_write_snd;
assign spec_mem_fst_addr = spec_mem_read ? spec_mem_read_fst_addr : spec_mem_write_fst_addr;
assign spec_mem_snd_addr = spec_mem_read ? spec_mem_read_snd_addr : spec_mem_write_snd_addr;

logic [31:0] fst_mask, snd_mask;
assign fst_mask = {
    {8{spec_mem_write_fst_be[3]}}, {8{spec_mem_write_fst_be[2]}},
    {8{spec_mem_write_fst_be[1]}}, {8{spec_mem_write_fst_be[0]}}
};
assign snd_mask = {
    {8{spec_mem_write_snd_be[3]}}, {8{spec_mem_write_snd_be[2]}},
    {8{spec_mem_write_snd_be[1]}}, {8{spec_mem_write_snd_be[0]}}
};

logic fst_mem_cmp;
assign fst_mem_cmp = (spec_mem_write == data_we_o) && (spec_mem_read == ~data_we_o) &&
                     (data_addr_o == spec_mem_fst_addr) &&
                     (data_we_o ->
                        (data_wdata_o & fst_mask) == (spec_mem_write_fst_wdata & fst_mask));
logic snd_mem_cmp;
assign snd_mem_cmp = (spec_mem_write_snd == data_we_o) && (spec_mem_read_snd == ~data_we_o) &&
                     (data_addr_o == spec_mem_snd_addr) &&
                     (data_we_o ->
                        (data_wdata_o & snd_mask) == (spec_mem_write_snd_wdata & snd_mask));

////////////////////// Compare //////////////////////

logic addr_match; // Register write index match
logic data_match; // Register write data match
logic nowrite; // Neither spec nor dut writing to RF
logic csrs_match; // CSR match
logic csrs_didnt_change;
logic pc_match; // PC match
logic finishing_executed; // Finishing normal case

`define INSTR `CR.instr_rdata_id

logic wbexc_is_checkable_csr;
logic ex_is_checkable_csr;
assign ex_is_checkable_csr = ~(
  // Performance counters and such, not specified in Sail
  ((CSR_MHPMCOUNTER3H <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMCOUNTER31H)) |
  ((CSR_MHPMCOUNTER3 <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMCOUNTER31)) |
  ((CSR_MHPMEVENT3 <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMEVENT31)) |
  (`CSR_ADDR == CSR_MCYCLE) | (`CSR_ADDR == CSR_MCYCLEH) |
  (`CSR_ADDR == CSR_MCOUNTINHIBIT) |
  (`CSR_ADDR == CSR_MINSTRET) | (`CSR_ADDR == CSR_MINSTRETH) |

  // Ibex but not Sail:
  (`CSR_ADDR == CSR_SECURESEED) |
  (`CSR_ADDR == CSR_CPUCTRL) |
  (`CSR_ADDR == CSR_CDBG_CTRL) |

  // Sail but not Ibex:
  (`CSR_ADDR == 12'h30a) | // MENVCFG
  (`CSR_ADDR == 12'h31a) | // MENVCFGH
  (`CSR_ADDR == 12'h310) | // MSTATUSH
  (`CSR_ADDR == 12'hF15) | // MCONFIGPTR 

  // Specified to be illegal in Sail but isn't in Ibex:
  (CSR_PMPCFG0 <= `CSR_ADDR && `CSR_ADDR <= CSR_PMPCFG3) |
  (CSR_PMPADDR0 <= `CSR_ADDR && `CSR_ADDR <= CSR_PMPADDR15) |

  // We don't verify stkz
  (`CSR_ADDR == CSR_MSHWM) | (`CSR_ADDR == CSR_MSHWMB)
);

////////////////////// Decompression Invariant Defs //////////////////////

logic [31:0] decompressed_instr;
logic decompressed_instr_illegal;
ibex_compressed_decoder decompression_assertion_decoder(
    .clk_i,
    .rst_ni,
    .valid_i(1'b1),
    .instr_i(idex_compressed_instr),
    .instr_o(decompressed_instr),
    .is_compressed_o(),
    .illegal_instr_o(decompressed_instr_illegal),
    .cheri_pmode_i
);

logic [31:0] decompressed_instr_2;
logic decompressed_instr_illegal_2;
ibex_compressed_decoder decompression_assertion_decoder_2(
    .clk_i,
    .rst_ni,
    .valid_i(1'b1),
    .instr_i(wbexc_instr),
    .instr_o(decompressed_instr_2),
    .is_compressed_o(wbexc_is_compressed),
    .illegal_instr_o(decompressed_instr_illegal_2),
    .cheri_pmode_i
);

////////////////////// IRQ + Memory Protocols //////////////////////
`include "protocol/irqs.sv"
`include "protocol/mem.sv"

////////////////////// Following //////////////////////
`include "peek/pcc.sv" // PCC.address
`include "peek/abs.sv" // Abstract state
`include "peek/capdti.sv" // Capability DTI
`include "peek/mem.sv" // Memory tracking
`include "peek/follower.sv" // Pipeline follower
`include "spec_instance.sv" // Instantiate the specification

////////////////////// Proof helpers ///////////////////////
`include "peek/compare_helper.sv"

////////////////////// Proof //////////////////////
`undef INSTR
`define INSTR wbexc_decompressed_instr
`include "../build/psgen.sv"

endmodule
