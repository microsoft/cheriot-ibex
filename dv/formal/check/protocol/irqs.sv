// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following give the protocol that IRQs must follow.
*/

typedef struct packed {
  logic        irq_software;
  logic        irq_timer;
  logic        irq_external;
  logic [14:0] irq_fast;
	logic        irq_nmi;
} extended_irqs_t;

extended_irqs_t extended_mip;
assign extended_mip.irq_software = irq_software_i;
assign extended_mip.irq_timer = irq_timer_i;
assign extended_mip.irq_external = irq_external_i;
assign extended_mip.irq_fast = irq_fast_i;
assign extended_mip.irq_nmi = irq_nm_i;

// IRQs must remain active until they are cleared by some MMIO memory request
// The alternative is that IRQs disappear after just one cycle or something
MIPFair: assume property (
	$past(extended_mip) == ($past(extended_mip) & extended_mip) || data_gnt_i
);

`define WFI_BOUND 20
// If we are asleep we must eventually wake up. This is validated by the WFIStart assumption,
// which ensures that this is actually possible. We make the time bounded instead of s_eventually
// for conclusivity purposes.
WFIWakeUp: assume property (`IDC.ctrl_fsm_cs == SLEEP |-> ##[0:`WFI_BOUND] `IDC.irq_pending_i);
