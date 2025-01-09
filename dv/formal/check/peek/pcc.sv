// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following implements PCC.address. As per the Sail, PCC.address != PC, but it is also not
needed if you are willing to store the bounds in the decompressed form, as cheriot-ibex does.
This creates a problem for DTI checks, so we track PCC.address here. This code is the data mirror
for the code in ibex_cs_registers.sv. It is more or less identical.
*/

always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
        pcc_address_q <= 0;
    end else begin
        pcc_address_q <= pcc_address_d;
    end
end

always_comb begin
    if (`CSR.csr_save_cause_i) begin 
        pcc_address_d = `CSR.mtvec_q;
    end else if (`CSR.csr_restore_mret_i) begin
        pcc_address_d = `CSR.mepc_q;
    end else if (`CSR.cheri_branch_req_i) begin
        pcc_address_d = `CE.rf_rdata_a;
    end else begin
        pcc_address_d = pcc_address_q;
    end
end
