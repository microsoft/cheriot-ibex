// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

typedef struct packed {
    logic mie;
    logic mpie;
    logic tw;
    logic mprv;
    logic [1:0] mpp;
} mstatus_t;

module spec_api #(
    parameter int unsigned NREGS = 32,
    parameter int unsigned PMPNumRegions = 4
) (
    input t_MainMode main_mode,

    input t_Capability regs_i[31:1],

    output logic wx_en_o,
    output t_Capability wx_o,
    output logic [4:0] wx_addr_o,

    input logic [31:0] nextpc_i,
    input logic [31:0] pc_i,
    output logic [31:0] pc_o,

    input logic [31:0] misa_i,
    input logic [31:0] mip_i,

    input logic nmi_i,
    input logic nmi_mode_i,
    output logic nmi_mode_o,
    input mstatus_t mstack_i,
    output mstatus_t mstack_o,
    input logic [31:0] mstack_cause_i,
    output logic [31:0] mstack_cause_o,
    input logic [31:0] mstack_epc_i,
    output logic [31:0] mstack_epc_o,

    input logic [31:0] mvendor_id_i,
    input logic [31:0] march_id_i,
    input logic [31:0] mimp_id_i,
    input logic [31:0] mhart_id_i,
    input logic [31:0] mconfigptr_i,

    input logic [31:0] mseccfg_i,
    output logic [31:0] mseccfg_o,
    input logic [7:0] pmp_cfg_i[PMPNumRegions],
    output logic [7:0] pmp_cfg_o[PMPNumRegions],
    input logic [31:0] pmp_addr_i[PMPNumRegions],
    output logic [31:0] pmp_addr_o[PMPNumRegions],

    input logic [31:0] mie_i,
    output logic [31:0] mie_o,
    input t_Privilege priv_i,
    output t_Privilege priv_o,
    input mstatus_t mstatus_i,
    output mstatus_t mstatus_o,
    input logic [31:0] mcause_i,
    output logic [31:0] mcause_o,
    input logic [63:0] mcycle_i,
    output logic [63:0] mcycle_o,
    input logic [31:0] mtval_i,
    output logic [31:0] mtval_o,
    input t_Capability mtvec_i,
    output t_Capability mtvec_o,
    input logic [31:0] mscratch_i,
    output logic [31:0] mscratch_o,
    input t_Capability mepc_i,
    output t_Capability mepc_o,
    input logic [31:0] mshwmb_i,
    output logic [31:0] mshwmb_o,
    input logic [31:0] mshwm_i,
    output logic [31:0] mshwm_o,
    input logic [31:0] mcounteren_i,
    output logic [31:0] mcounteren_o,
    input t_Capability pcc_i,
    output t_Capability pcc_o,
    input t_Capability mscratchc_i,
    output t_Capability mscratchc_o,
    input t_Capability mtdc_i,
    output t_Capability mtdc_o,

    input logic [31:0] insn_bits,
    output logic int_err_o,

    output logic mem_read_o,
    output logic mem_read_snd_gran_o,
    output logic[31:0] mem_read_fst_addr_o,
    output logic[31:0] mem_read_snd_addr_o,
    input logic[31:0] mem_read_fst_rdata_i,
    input logic[31:0] mem_read_snd_rdata_i,
    input logic mem_read_tag_i,

    output logic mem_revoke_en_o,
    output logic[31:0] mem_revoke_granule_o,
    input logic mem_revoke_i,

    output logic mem_write_o,
    output logic mem_write_snd_gran_o,
    output logic[31:0] mem_write_fst_addr_o,
    output logic[31:0] mem_write_snd_addr_o,
    output logic[31:0] mem_write_fst_wdata_o,
    output logic[31:0] mem_write_snd_wdata_o,
    output logic [3:0] mem_write_fst_be_o,
    output logic [3:0] mem_write_snd_be_o,
    output logic mem_write_tag_o
);

bit wC_sail_invoke[0:0];
logic [63:0] wC_sail_invoke_arg_0[0:0];
t_Capability wC_sail_invoke_arg_1[0:0];
logic wX_sail_invoke[0:0];
logic [63:0] wX_sail_invoke_arg_0[0:0];
logic [31:0] wX_sail_invoke_arg_1[0:0];
assign wx_en_o = wX_sail_invoke[0] | wC_sail_invoke[0];
assign wx_addr_o = wX_sail_invoke[0] ? wX_sail_invoke_arg_0[0][4:0] : wC_sail_invoke_arg_0[0][4:0];
assign wx_o = wX_sail_invoke[0] ? dataCap(wX_sail_invoke_arg_1[0]) : encodeDecodePermsOf(wC_sail_invoke_arg_1[0]);

logic write_ram_sail_invoke[1:0];
logic [31:0] write_ram_sail_invoke_arg_1[1:0];
logic [31:0] write_ram_sail_invoke_arg_2[1:0];
logic [3:0] write_ram_sail_invoke_arg_3[1:0];
assign mem_write_o = write_ram_sail_invoke[0];
assign mem_write_snd_gran_o = write_ram_sail_invoke[1];
assign mem_write_fst_addr_o = write_ram_sail_invoke_arg_1[0];
assign mem_write_snd_addr_o = write_ram_sail_invoke_arg_1[1];
assign mem_write_fst_wdata_o = write_ram_sail_invoke_arg_2[0];
assign mem_write_snd_wdata_o = write_ram_sail_invoke_arg_2[1];
assign mem_write_fst_be_o = write_ram_sail_invoke_arg_3[0];
assign mem_write_snd_be_o = write_ram_sail_invoke_arg_3[1];

logic read_ram_sail_invoke[1:0];
logic [31:0] read_ram_sail_invoke_ret[1:0];
logic [31:0] read_ram_sail_invoke_arg_1[1:0];
assign mem_read_o = read_ram_sail_invoke[0];
assign mem_read_snd_gran_o = read_ram_sail_invoke[1];
assign mem_read_fst_addr_o = read_ram_sail_invoke_arg_1[0];
assign mem_read_snd_addr_o = read_ram_sail_invoke_arg_1[1];
assign read_ram_sail_invoke_ret[0] = mem_read_fst_rdata_i;
assign read_ram_sail_invoke_ret[1] = mem_read_snd_rdata_i;


bit mem_read_cap_revoked_sail_invoke[0:0];
bit mem_read_cap_revoked_sail_invoke_ret[0:0];
logic [31:0] mem_read_cap_revoked_sail_invoke_arg_0[0:0];
assign mem_revoke_en_o = mem_read_cap_revoked_sail_invoke[0];
assign mem_revoke_granule_o = mem_read_cap_revoked_sail_invoke_arg_0[0];
assign mem_read_cap_revoked_sail_invoke_ret[0] = mem_revoke_i;

bit __WriteRAM_Meta_sail_invoke_arg_2[0:0];
assign mem_write_tag_o = __WriteRAM_Meta_sail_invoke_arg_2[0];
bit __ReadRAM_Meta_sail_invoke_ret[0:0];
assign __ReadRAM_Meta_sail_invoke_ret[0] = mem_read_tag_i;

t_MainResult main_result;

t_Mstatus mstatus_out;
assign mstatus_o.mie = mstatus_out.bits[3];
assign mstatus_o.mpie = mstatus_out.bits[7];
assign mstatus_o.tw = mstatus_out.bits[21];
assign mstatus_o.mprv = mstatus_out.bits[17];
assign mstatus_o.mpp = mstatus_out.bits[12:11];

t_Mcause mcause_out;
assign mcause_o = mcause_out.bits;

t_Minterrupts mie_out;
assign mie_o = mie_out.bits;

t_Counteren mcounteren_out;
assign mcounteren_o = mcounteren_out.bits;

t_Pmpcfg_ent pmpcfg_n_in[63:0];
logic [31:0] pmpaddr_n_in[63:0];
t_Pmpcfg_ent pmpcfg_n_out[63:0];
logic [31:0] pmpaddr_n_out[63:0];
for (genvar i = 0; i < 64; i++) begin: g_pmp_bind
    if (i < PMPNumRegions) begin: g_pmp_bind_real
        assign pmpcfg_n_in[i] = '{bits: pmp_cfg_i[i]};
        assign pmpaddr_n_in[i] = pmp_addr_i[i];

        assign pmp_cfg_o[i] = pmpcfg_n_out[i].bits[7:0];
        assign pmp_addr_o[i] = pmpaddr_n_out[i];
    end else begin: g_pmp_bind_zero
        // These shouldn't ever be used anyway
        assign pmpcfg_n_in[i] = '{bits: 0};
        assign pmpaddr_n_in[i] = 0;
    end
end

t_Mseccfg_ent mseccfg_out;
assign mseccfg_o = mseccfg_out.bits;

t_Mcause mstack_cause_out;
t_Mstatus mstack_out;
assign mstack_cause_o = mstack_cause_out.bits;
assign mstack_o.mie = mstack_out.bits[3];
assign mstack_o.mpie = mstack_out.bits[7];
assign mstack_o.tw = mstack_out.bits[21];
assign mstack_o.mprv = mstack_out.bits[17];
assign mstack_o.mpp = mstack_out.bits[12:11];

sail_ibexspec spec_i(
    .cur_inst_in(insn_bits),
    .cur_inst_out(),
    .cur_privilege_in(priv_i),
    .cur_privilege_out(priv_o),
    .instbits_in(insn_bits),
    .instbits_out(),
    .marchid_in(march_id_i),
    .marchid_out(),
    .mcause_in('{bits: mcause_i}),
    .mcause_out,
    .mconfigptr_in(mconfigptr_i),
    .mconfigptr_out(),
    .mcounteren_in('{ bits: mcounteren_i }),
    .mcounteren_out,
    .mcountinhibit_in(),
    .mcountinhibit_out(),
    .mcycle_in(mcycle_i),
    .mcycle_out(mcycle_o),
    .medeleg_in('{bits: 32'h0}),
    .medeleg_out(),
    .menvcfg_in('{bits: 32'h0}),
    .menvcfg_out(),
    .MEPCC_in(mepc_i),
    .MEPCC_out(mepc_o),
    .mhartid_in(mhart_id_i),
    .mhartid_out(),
    .mideleg_in(),
    .mideleg_out(),
    .mie_in('{bits: mie_i}),
    .mie_out,
    .mimpid_in(mimp_id_i),
    .mimpid_out(),
    .minstret_in(),
    .minstret_out(),
    .minstret_increment_in(),
    .minstret_increment_out(),
    .mip_in('{bits: mip_i}),
    .mip_out(),
    .nmi_in(nmi_i),
    .nmi_mode_in(nmi_mode_i),
    .nmi_mode_out(nmi_mode_o),
    .mstack_in('{bits:
        (32'(mstack_i.mie) << 3) |
        (32'(mstack_i.mpie) << 7) |
        (32'(mstack_i.tw) << 21) |
        (32'(mstack_i.mprv) << 17) |
        (32'(mstack_i.mpp) << 11)
    }),
    .mstack_out,
    .mstack_epc_in(mstack_epc_i),
    .mstack_epc_out(mstack_epc_o),
    .mstack_cause_in('{bits: mstack_cause_i}),
    .mstack_cause_out,
    .misa_in('{bits: misa_i}),
    .misa_out(),
    .mscratch_in(mscratch_i),
    .mscratch_out(mscratch_o),
    .MScratchC_in(mscratchc_i),
    .MScratchC_out(mscratchc_o),
    .MTDC_in(mtdc_i),
    .MTDC_out(mtdc_o),
    .mstatus_in('{bits:
        (32'(mstatus_i.mie) << 3) |
        (32'(mstatus_i.mpie) << 7) |
        (32'(mstatus_i.tw) << 21) |
        (32'(mstatus_i.mprv) << 17) |
        (32'(mstatus_i.mpp) << 11)
    }),
    .mstatus_out,
    .mstatush_in('{bits: 32'b0}),
    .mstatush_out(),
    .mtval_in(mtval_i),
    .mtval_out(mtval_o),
    .MTCC_in(mtvec_i),
    .MTCC_out(mtvec_o),
    .MSHWMB_in(mshwmb_i),
    .MSHWMB_out(mshwmb_o),
    .MSHWM_in(mshwm_i),
    .MSHWM_out(mshwm_o),
    .mvendorid_in(mvendor_id_i),
    .mvendorid_out(),
    .nextPC_in(nextpc_i),
    .nextPC_out(pc_o),
    .nextPCC_in(pcc_i),
    .nextPCC_out(pcc_o),
    .PC_in(pc_i),
    .PC_out(),
    .PCC_in(pcc_i),
    .PCC_out(),
    .mseccfg_in('{bits: mseccfg_i}),
    .mseccfg_out,
    .mseccfgh_in(32'h0),
    .mseccfgh_out(),
    .pmpaddr_n_in,
    .pmpaddr_n_out,
    .pmpcfg_n_in,
    .pmpcfg_n_out,
    .scause_in(),
    .scause_out(),
    .scounteren_in(),
    .scounteren_out(),
    .sedeleg_in(),
    .sedeleg_out(),
    .senvcfg_in(),
    .senvcfg_out(),
    .sepc_in(),
    .sepc_out(),
    .sideleg_in(),
    .sideleg_out(),
    .sscratch_in(),
    .sscratch_out(),
    .stval_in(),
    .stval_out(),
    .stvec_in(),
    .stvec_out(),
    .tselect_in(),
    .tselect_out(),
    .x1_in(regs_i[1]),
    .x1_out(),
    .x2_in(regs_i[2]),
    .x2_out(),
    .x3_in(regs_i[3]),
    .x3_out(),
    .x4_in(regs_i[4]),
    .x4_out(),
    .x5_in(regs_i[5]),
    .x5_out(),
    .x6_in(regs_i[6]),
    .x6_out(),
    .x7_in(regs_i[7]),
    .x7_out(),
    .x8_in(regs_i[8]),
    .x8_out(),
    .x9_in(regs_i[9]),
    .x9_out(),
    .x10_in(regs_i[10]),
    .x10_out(),
    .x11_in(regs_i[11]),
    .x11_out(),
    .x12_in(regs_i[12]),
    .x12_out(),
    .x13_in(regs_i[13]),
    .x13_out(),
    .x14_in(regs_i[14]),
    .x14_out(),
    .x15_in(regs_i[15]),
    .x15_out(),
    .x16_in(regs_i[16]),
    .x16_out(),
    .x17_in(regs_i[17]),
    .x17_out(),
    .x18_in(regs_i[18]),
    .x18_out(),
    .x19_in(regs_i[19]),
    .x19_out(),
    .x20_in(regs_i[20]),
    .x20_out(),
    .x21_in(regs_i[21]),
    .x21_out(),
    .x22_in(regs_i[22]),
    .x22_out(),
    .x23_in(regs_i[23]),
    .x23_out(),
    .x24_in(regs_i[24]),
    .x24_out(),
    .x25_in(regs_i[25]),
    .x25_out(),
    .x26_in(regs_i[26]),
    .x26_out(),
    .x27_in(regs_i[27]),
    .x27_out(),
    .x28_in(regs_i[28]),
    .x28_out(),
    .x29_in(regs_i[29]),
    .x29_out(),
    .x30_in(regs_i[30]),
    .x30_out(),
    .x31_in(regs_i[31]),
    .x31_out(),

    .wX_sail_invoke,
    .wX_sail_invoke_ret(),
    .wX_sail_invoke_arg_0,
    .wX_sail_invoke_arg_1,

    .wC_sail_invoke,
    .wC_sail_invoke_ret(),
    .wC_sail_invoke_arg_0,
    .wC_sail_invoke_arg_1,

    .write_ram_sail_invoke,
    .write_ram_sail_invoke_ret(),
    .write_ram_sail_invoke_arg_0(),
    .write_ram_sail_invoke_arg_1,
    .write_ram_sail_invoke_arg_2,
    .write_ram_sail_invoke_arg_3,

    .read_ram_sail_invoke,
    .read_ram_sail_invoke_ret,
    .read_ram_sail_invoke_arg_0(),
    .read_ram_sail_invoke_arg_1,

    .mem_read_cap_revoked_sail_invoke,
    .mem_read_cap_revoked_sail_invoke_ret,
    .mem_read_cap_revoked_sail_invoke_arg_0,

    .__ReadRAM_Meta_sail_invoke(),
    .__ReadRAM_Meta_sail_invoke_ret,
    .__ReadRAM_Meta_sail_invoke_arg_0(),
    .__ReadRAM_Meta_sail_invoke_arg_1(),
    .__WriteRAM_Meta_sail_invoke(),
    .__WriteRAM_Meta_sail_invoke_ret(),
    .__WriteRAM_Meta_sail_invoke_arg_0(),
    .__WriteRAM_Meta_sail_invoke_arg_1(),
    .__WriteRAM_Meta_sail_invoke_arg_2,

    .main_result(main_result),
    .insn_bits(insn_bits),
    .mode(main_mode)
);

assign int_err_o = spec_i.sail_reached_unreachable |
                   spec_i.sail_have_exception |
                   (main_result != MAINRES_OK);

endmodule
