// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This file implements the abstract state for Ibex, it maps Ibex types to Sail types.
pre_* is the pre_state, i.e. if an instruction is starting to run now, this is the architectural state that it observes.
post_* is the post_state, i.e. if an instruction starts in the next cycle, this is the architectural state that it will observe.
*/

/////////////// GPR Pre-State ///////////////

t_Capability fwd_data;
assign fwd_data = regcap2sail(`CR.rf_wcap_fwd_wb, `CR.rf_wdata_fwd_wb);


for (genvar i = 0; i < 32; i++) begin: g_pre_regs
    t_Capability rf_data;
    assign rf_data =
        revoke(
            regcap2sail(`RF.rf_cap[i], `RF.rf_reg[i]),
            (0 < i && i < 16 ? `RF.trvk_dec[i] : 1'b0) & `RF.trvk_en_i & `RF.trvk_clrtag_i
        );
    assign pre_regs[i] = `CR.rf_write_wb && `CR.rf_waddr_wb == i && i > '0 ? fwd_data : rf_data;
end

// FIXME: Redefined from ibex_cs_registers
typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
} status_t;

/////////////// CSR Pre-State ///////////////

assign pre_pc = wbexc_handling_irq? `CR.pc_if:`CR.pc_id;
assign pre_nextpc = `CR.pc_id + (`CR.instr_is_compressed_id ? 2 : 4);
assign pre_priv = `CSR.priv_lvl_q == PRIV_LVL_M ? Machine : User;
assign pre_mstatus = '{
    mie: `CSR.mstatus_q.mie,
    mpie: `CSR.mstatus_q.mpie,
    tw: `CSR.mstatus_q.tw,
    mprv: `CSR.mstatus_q.mprv,
    mpp: `CSR.mstatus_q.mpp
};
assign pre_mip = irqsToMInterrupts(`CSR.mip);
assign pre_nmi = irq_nm_i;
assign pre_nmi_mode = `IDC.nmi_mode_q;
assign pre_mie = irqsToMInterrupts(`CSR.mie_q);
assign pre_mcause = widenMCause(`CSR.mcause_q);
assign pre_mtval = `CSR.mtval_q;
assign pre_mscratch = `CSR.mscratch_q;
assign pre_mcounteren = '0; // ibex hardwires to zero
assign pre_mtvec = regcap2sail(`CSR.mtvec_cap, `CSR.mtvec_q);
assign pre_mepc = regcap2sail(`CSR.mepc_cap, `CSR.mepc_q);
assign pre_mtdc = regcap2sail(`CSRG.mtdc_cap, `CSRG.mtdc_data);
assign pre_mscratchc = regcap2sail(`CSRG.mscratchc_cap, `CSRG.mscratchc_data);
assign pre_pcc = pcc2sail(`CR.pcc_cap_r, pcc_address_q);
assign pre_mstack = '{
    mpie: `CSR.mstack_q.mpie,
    mpp: `CSR.mstack_q.mpp,
    mie: '0,
    tw: '0,
    mprv: '0
};
assign pre_mstack_cause = widenMCause(`CSR.mstack_cause_q);
assign pre_mstack_epc = `CSR.mstack_epc_q;
// assign pre_mshwm = `CSR.mshwm_q;
// assign pre_mshwmb = `CSR.mshwmb_q;

/////////////// CSR Post-State ///////////////

reg_cap_t mepc_cap_next;
always_comb begin
    if (`CSR.csr_save_cause_i)
        mepc_cap_next <= `CSRG.pcc_exc_cap;
    else if (cheri_pmode_i & `CSR.mepc_en)
        mepc_cap_next <= NULL_REG_CAP;
    else if (`CSR.mepc_en_cheri)
        mepc_cap_next <= `CSR.cheri_csr_wcap_i;
    else
        mepc_cap_next <= `CSR.mepc_cap;
end

t_Capability csr_incoming_cap;
assign csr_incoming_cap = regcap2sail(`CSR.cheri_csr_wcap_i, `CSR.cheri_csr_wdata_i);

// Bit 0 of fetch addr n is always cleared.
assign post_pc = `IF.branch_req ? {`IF.fetch_addr_n[31:1], 1'b0} : `CSR.pc_if_i;
assign post_nmi_mode = `IDC.nmi_mode_d;
assign post_mie = `CSR.mie_en ? irqsToMInterrupts(`CSR.mie_d) : pre_mie;
assign post_priv = `CSR.priv_lvl_d == PRIV_LVL_M ? Machine : User;
assign post_mstatus = `CSR.mstatus_en_combi ? '{
    mie: `CSR.mstatus_d_combi.mie,
    mpie: `CSR.mstatus_d_combi.mpie,
    tw: `CSR.mstatus_d_combi.tw,
    mprv: `CSR.mstatus_d_combi.mprv,
    mpp: `CSR.mstatus_d_combi.mpp
}:pre_mstatus;
assign post_mcause = `CSR.mcause_en ? widenMCause(`CSR.mcause_d) : pre_mcause;
assign post_mtval = `CSR.mtval_en ? `CSR.mtval_d : pre_mtval;
assign post_mscratch = `CSR.mscratch_en ? `CSR.csr_wdata_int : pre_mscratch;
assign post_mcounteren = '0;
assign post_mtvec = `CSR.mtvec_en_combi ?
    regcap2sail(`CSR.mtvec_en_cheri ? `CSR.cheri_csr_wcap_i : `CSR.mtvec_cap, `CSR.mtvec_d_combi):
    pre_mtvec;
assign post_mepc = `CSR.mepc_en_combi ? regcap2sail(mepc_cap_next, `CSR.mepc_d_combi) : pre_mepc;
assign post_mtdc = `CSRG.mtdc_en_cheri ? csr_incoming_cap : pre_mtdc;
assign post_mscratchc = `CSRG.mscratchc_en_cheri ? csr_incoming_cap : pre_mscratchc;
assign post_pcc = pcc2sail(`CSR.pcc_cap_d, pcc_address_d);
assign post_mstack = `CSR.mstack_en ? '{
    mpie: `CSR.mstack_d.mpie,
    mpp: `CSR.mstack_d.mpp,
    mie: '0,
    tw: '0,
    mprv: '0
} : pre_mstack;
assign post_mstack_cause = `CSR.mstack_en ? widenMCause(`CSR.mstack_cause_d) : pre_mstack_cause;
assign post_mstack_epc = `CSR.mstack_en ? `CSR.mstack_epc_d : pre_mstack_epc;
// assign post_mshwm = `CSR.mshwm_en_combi ? `CSR.mshwm_d : pre_mshwm;
// assign post_mshwmb = `CSR.mshwmb_en ? {`CSR.csr_wdata_int[31:4], 4'h0} : pre_mshwmb;

assign post_trvk_regs[0] = nullCap();
for (genvar i = 1; i < 16; i++) begin: g_post_trvk_regs
    assign post_trvk_regs[i] =
        revoke(regcap2sail(`RF.rf_cap[i], `RF.rf_reg[i]), `RF.trvk_dec[i] & `RF.trvk_en_i & `RF.trvk_clrtag_i);
end

/////////////// Encoders ///////////////

function automatic logic [31:0] irqsToMInterrupts(irqs_t irqs);
    return
        (32'(irqs.irq_software) << 3) |
        (32'(irqs.irq_timer) << 7) |
        (32'(irqs.irq_external) << 11) |
        (32'(irqs.irq_fast) << 16);
endfunction

function automatic logic[31:0] widenMCause(logic [5:0] mcause);
    return {mcause[5], 26'b0, mcause[4:0]};
endfunction
