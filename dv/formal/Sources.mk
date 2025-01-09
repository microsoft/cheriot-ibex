# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# Original Author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

SAIL_XLEN := riscv_xlen32.sail

SAIL_CHECK_SRCS = riscv_addr_checks_common.sail $(CHERI)/cheri_addr_checks.sail $(CHERI)/cheri_misa_ext.sail
SAIL_DEFAULT_INST = riscv_insts_base.sail riscv_insts_cext.sail riscv_insts_mext.sail riscv_insts_zicsr.sail
SAIL_CHERI_INSTS = $(CHERI)/cheri_insts_begin.sail $(CHERI)/cheri_insts.sail $(CHERI)/cheri_insts_cext.sail $(CHERI)/cheri_insts_end.sail

SAIL_SEQ_INST  = $(SAIL_DEFAULT_INST) $(SAIL_CHERI_INSTS) riscv_jalr_seq.sail

SAIL_SEQ_INST_SRCS  = riscv_insts_begin.sail $(SAIL_SEQ_INST) riscv_insts_end.sail $(CHERI)/cheri_decode_ext.sail

SAIL_SYS_SRCS =  riscv_csr_map.sail
SAIL_SYS_SRCS += $(CHERI)/cheri_sys_exceptions.sail
SAIL_SYS_SRCS += riscv_sync_exception.sail riscv_csr_ext.sail riscv_sys_control.sail
SAIL_SYS_SRCS += $(SAIL_CHECK_SRCS)

PRELUDE = prelude.sail $(SAIL_XLEN) $(CHERI)/cheri_prelude.sail $(CHERI)/cheri_types.sail $(CHERI)/cheri_cap_common.sail $(CHERI)/cheri_mem_metadata.sail prelude_mem.sail

# SAIL_REGS_SRCS = riscv_reg_type.sail riscv_regs.sail riscv_pc_access.sail riscv_sys_regs.sail
SAIL_REGS_SRCS = $(CHERI)/cheri_reg_type.sail
SAIL_REGS_SRCS += riscv_csr_map.sail $(CHERI)/cheri_scr_map.sail
SAIL_REGS_SRCS += $(CHERI)/cheri_vmem_types.sail
SAIL_REGS_SRCS += riscv_regs.sail riscv_sys_regs.sail
SAIL_REGS_SRCS += riscv_pmp_regs.sail riscv_pmp_control.sail
SAIL_REGS_SRCS += $(CHERI)/cheri_sys_regs.sail $(CHERI)/cheri_regs.sail
SAIL_REGS_SRCS += $(CHERI)/cheri_pc_access.sail

SAIL_ARCH_SRCS = $(PRELUDE)
SAIL_ARCH_SRCS += riscv_types_common.sail $(CHERI)/cheri_riscv_types.sail riscv_types.sail
SAIL_ARCH_SRCS += $(SAIL_REGS_SRCS) $(SAIL_SYS_SRCS) riscv_platform.sail
SAIL_ARCH_SRCS += riscv_mem.sail $(CHERI)/cheri_mem.sail

SAIL_SRCS      = $(addprefix $(SAIL_RISCV_MODEL_DIR)/,$(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS))

COMPRESSED_INSTRS=C_J C_JALR C_LW C_ADDIW C_LI C_ANDI C_BEQZ C_LD C_ILLEGAL C_AND C_JAL C_MV C_XOR \
					C_CSC C_CIncAddr16CSP C_ADD C_CSCSP C_EBREAK C_CLC C_SDSP C_ADDI4SPN C_CJR C_SW C_SUB \
					C_SWSP C_SRLI C_LDSP C_SD C_SRAI C_LUI C_OR C_SUBW C_CIncAddr4CSPN C_JR C_CJALR C_ADDI \
					C_ADDW C_BNEZ C_ADDI16SP C_NOP C_CJAL C_SLLI C_CLCSP
