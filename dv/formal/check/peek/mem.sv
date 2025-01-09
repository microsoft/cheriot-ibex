// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This file implements the tracking of ibex memory. It (by assumption) sets data_rvalid_i to the corresponding value that was
sent to the spec. The interpretation of the signals used is justified in the proofs.
*/

logic has_snd_req;
assign has_snd_req = mem_gnt_snd_d | (mem_gnt_fst_q & `CR.data_req_out);

logic outstanding_resp;
assign outstanding_resp = `CR.outstanding_load_wb | `CR.outstanding_store_wb;

/*
Some definitions:
- An 'early response' is a response made to a memory instruction before the instruction has progressed to the WB stage,
  i.e. while it is still in the ID/EX stage. This is only possible for multi-request instructions, and only one
  early response can be made.
- A 'late response' is a response received during the WB stage. There can be at most one late response, since
  if a memory instruction sends two requests, it won't go to WB until it has sent one request.
Responses are given in the order they are requested, so it suffices to check if WB is waiting on a response.
*/
logic early_resp, late_resp;
assign early_resp = data_rvalid_i & ~outstanding_resp;
assign late_resp = data_rvalid_i & outstanding_resp;

// If we receive an early response, give it the data sent to the spec directly
LoadMemEarlyResp: assume property (
    early_resp |-> data_rdata_i == {spec_mem_read_tag, spec_mem_read_fst_rdata}
);

// If we have a late response, and this is the first response send the low spec data
LoadMemLateRespFirst: assume property (
    late_resp & ~wbexc_mem_had_snd_req |-> data_rdata_i == {wbexc_spec_mem_read_tag, wbexc_spec_mem_read_fst_rdata}
);

// If we have a late response, and this is the second response, send the high spec data
LoadMemLateRespSecond: assume property (
    late_resp & wbexc_mem_had_snd_req |-> data_rdata_i == {wbexc_spec_mem_read_tag, wbexc_spec_mem_read_snd_rdata}
);

// The spec read data cannot change while an instruction is running, only when there is a new one
// Note these values are undriven, they are not from the spec as the name would suggest
SpecReadDataKeep: assume property (~instr_will_progress |=>
    $stable(spec_mem_read_fst_rdata) && $stable(spec_mem_read_snd_rdata) && $stable(spec_mem_read_tag)
);

logic[31:0] tsmap_heap_relative_ptr;
assign tsmap_heap_relative_ptr = spec_mem_revoke_addr - HeapBase;

logic[31:0] wbexc_tsmap_heap_relative_ptr;
logic[4:0] wbexc_tsmap_rdata_bit_idx;
logic[31:0] wbexc_tsmap_addr;
assign wbexc_tsmap_heap_relative_ptr = wbexc_spec_mem_revoke_addr - HeapBase;
assign wbexc_tsmap_rdata_bit_idx = wbexc_tsmap_heap_relative_ptr[7:3];
assign wbexc_tsmap_addr = wbexc_tsmap_heap_relative_ptr[31:8];

TRVKValue: assume property (
    $past(wbexc_tsmap_addr, 2) == tsmap_addr_o
    |->
    tsmap_rdata_i[$past(wbexc_tsmap_rdata_bit_idx, 2)] == $past(wbexc_spec_mem_revoke, 2)
);

TRVKZeroOutsideRange: assume property (
    spec_mem_revoke_en & (tsmap_heap_relative_ptr[31:8] >= TSMapSize) |-> ~spec_mem_revoke
);

assign mem_gnt_fst_d = mem_gnt_fst_q | data_gnt_i;
assign mem_gnt_snd_d = mem_gnt_snd_q | (data_gnt_i & mem_gnt_fst_q);

assign mem_req_fst_d = data_req_o & ~mem_gnt_fst_q;
assign mem_req_snd_d = data_req_o & mem_gnt_fst_q;

always @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni | instr_will_progress) begin
        mem_gnt_fst_q <= 1'b0;
        mem_gnt_snd_q <= 1'b0;
    end else begin
        mem_gnt_fst_q <= mem_gnt_fst_d;
        mem_gnt_snd_q <= mem_gnt_snd_d;
    end
end

assign mem_resp_d = mem_resp_q | (data_rvalid_i & ~outstanding_mem);

always @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni | instr_will_progress) begin
        mem_resp_q <= 1'b0;
    end else begin
        mem_resp_q <= mem_resp_d;
    end
end

`define ALT_LSU_STATE_COPY \
    .cheri_pmode_i, \
    .data_rvalid_i(1'b1), \
    .data_err_i(1'b0), \
    .data_we_q(`LSU.data_we_q), \
    .pmp_err_q(`LSU.pmp_err_q), \
    .lsu_err_q(`LSU.lsu_err_q), \
    .outstanding_resp_q(`LSU.outstanding_resp_q), \
    .resp_is_cap_q(`LSU.resp_is_cap_q), \
    .cheri_err_q(`LSU.cheri_err_q), \
    .resp_lc_clrperm_q(`LSU.resp_lc_clrperm_q), \
    .cap_lsw_err_q(`LSU.cap_lsw_err_q), \
    .lsu_rcap_o(),

alt_lsu #(.CHERIoTEn(1'b1), .MemCapFmt(1'b0), .CheriTBRE(1'b0)) alt_lsu_late_i (
    .cap_rx_fsm_q(`LSU.cap_rx_fsm_q),
    .data_rdata_i(
        ~wbexc_mem_had_snd_req ?
            {wbexc_spec_mem_read_tag, wbexc_spec_mem_read_fst_rdata} :
            {wbexc_spec_mem_read_tag, wbexc_spec_mem_read_snd_rdata}
    ),
    `ALT_LSU_STATE_COPY
    .data_type_q(`LSU.data_type_q),
    .rdata_offset_q(`LSU.rdata_offset_q),
    .data_sign_ext_q(`LSU.data_sign_ext_q),
    .rdata_q(`LSU.rdata_q),
    .cap_lsw_q(`LSU.cap_lsw_q)
);

t_Capability alt_lsu_late_res;
assign alt_lsu_late_res = regcap2sail(alt_lsu_late_i.lsu_rcap_o, alt_lsu_late_i.lsu_rdata_o[31:0]);

alt_lsu #(.CHERIoTEn(1'b1), .MemCapFmt(1'b0), .CheriTBRE(1'b0)) alt_lsu_very_early_i (
    .cap_rx_fsm_q(`LSU.resp_is_cap_q ? CRX_WAIT_RESP2 : CRX_IDLE),
    .data_rdata_i(
        ~(`LSU.split_misaligned_access | ex_is_mem_cap_instr) ?
            {spec_mem_read_tag, spec_mem_read_fst_rdata} :
            {spec_mem_read_tag, spec_mem_read_snd_rdata}
    ),
    `ALT_LSU_STATE_COPY
    .data_type_q(`LSU.lsu_type_i),
    .data_sign_ext_q(`LSU.lsu_sign_ext_i),
    .rdata_offset_q(`LSU.data_offset),
    .rdata_q(spec_mem_read_fst_rdata[31:8]),
    .cap_lsw_q({spec_mem_read_tag, spec_mem_read_fst_rdata})
);

t_Capability alt_lsu_very_early_res;
assign alt_lsu_very_early_res = regcap2sail(alt_lsu_very_early_i.lsu_rcap_o, alt_lsu_very_early_i.lsu_rdata_o[31:0]);

alt_lsu #(.CHERIoTEn(1'b1), .MemCapFmt(1'b0), .CheriTBRE(1'b0)) alt_lsu_early_i (
    .cap_rx_fsm_q(`LSU.cap_rx_fsm_q),
    .data_rdata_i({spec_mem_read_tag, spec_mem_read_snd_rdata}),
    `ALT_LSU_STATE_COPY
    .data_type_q(`LSU.data_type_q),
    .data_sign_ext_q(`LSU.data_sign_ext_q),
    .rdata_offset_q(`LSU.rdata_offset_q),
    .rdata_q(`LSU.rdata_q),
    .cap_lsw_q(`LSU.cap_lsw_q)
);

t_Capability alt_lsu_early_res;
assign alt_lsu_early_res = regcap2sail(alt_lsu_early_i.lsu_rcap_o, alt_lsu_early_i.lsu_rdata_o[31:0]);
