// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

`ifndef CMP_INSNS
`define CMP_INSNS

`define IS_ITYPE(idx) (`INSTR[6:0] == 7'b0010011 && `INSTR[14:12] == idx)
`define IS_ADDI `IS_ITYPE(3'b000)
`define IS_SLTI `IS_ITYPE(3'b010)
`define IS_SLTIU `IS_ITYPE(3'b011)
`define IS_XORI `IS_ITYPE(3'b100)
`define IS_ORI `IS_ITYPE(3'b110)
`define IS_ANDI `IS_ITYPE(3'b111)
`define IS_ANY_ITYPE ( \
    `IS_ADDI | `IS_SLTI | `IS_SLTIU | `IS_XORI | \
    `IS_ORI | `IS_ANDI \
)

`define IS_SLLI (`IS_ITYPE(3'b001) && `INSTR[31:25] == 7'b0000000)
`define IS_SRLI (`IS_ITYPE(3'b101) && `INSTR[31:25] == 7'b0000000)
`define IS_SRAI (`IS_ITYPE(3'b101) && `INSTR[31:25] == 7'b0100000)

`define IS_SHIFTIOP (`IS_SLLI | `IS_SRLI | `IS_SRAI)

`define IS_RTYPE_0(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0000000 && `INSTR[14:12] == idx)
`define IS_RTYPE_1(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0100000 && `INSTR[14:12] == idx)
`define IS_ADD `IS_RTYPE_0(3'b000)
`define IS_SUB `IS_RTYPE_1(3'b000)
`define IS_SLL `IS_RTYPE_0(3'b001)
`define IS_SLT `IS_RTYPE_0(3'b010)
`define IS_SLTU `IS_RTYPE_0(3'b011)
`define IS_XOR `IS_RTYPE_0(3'b100)
`define IS_SRL `IS_RTYPE_0(3'b101)
`define IS_SRA `IS_RTYPE_1(3'b101)
`define IS_OR `IS_RTYPE_0(3'b110)
`define IS_AND `IS_RTYPE_0(3'b111)

`define IS_FENCETYPE(idx) ( \
    `INSTR[31:25] == 4'b0000 && `INSTR[19:15] == 5'b00000 && \
    `INSTR[11:0] == 12'b000000001111 && `INSTR[14:12] == idx)
`define IS_FENCE (`INSTR[31:28] == 4'b0 && `INSTR[19:0] == 20'b0001111)
`define IS_FENCEI (`INSTR == 32'h100f)

`define IS_LOAD(idx) (`INSTR[6:0] == 7'b0000011 && `INSTR[14:12] == idx)
`define IS_LB `IS_LOAD(3'b000)
`define IS_LH `IS_LOAD(3'b001)
`define IS_LW `IS_LOAD(3'b010)
`define IS_LBU `IS_LOAD(3'b100)
`define IS_LHU `IS_LOAD(3'b101)
`define IS_LOADCAPIMM `IS_LOAD(3'b011)

`define IS_STORE(idx) (`INSTR[6:0] == 7'b0100011 && `INSTR[14:12] == idx)
`define IS_SB `IS_STORE(3'b000)
`define IS_SH `IS_STORE(3'b001)
`define IS_SW `IS_STORE(3'b010)
`define IS_STORECAPIMM `IS_STORE(3'b011)

`define IS_JAL (`INSTR[6:0] == 7'h6f)
`define IS_JALR (`INSTR[6:0] == 7'h67 && `INSTR[14:12] == 3'b0)

`define IS_MTYPE(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0000001 && `INSTR[14:12] == idx)
`define IS_MUL `IS_MTYPE(3'b000)
`define IS_MULH `IS_MTYPE(3'b001)
`define IS_MULHSH `IS_MTYPE(3'b010)
`define IS_MULHU `IS_MTYPE(3'b011)
`define IS_DIV `IS_MTYPE(3'b100)
`define IS_DIVU `IS_MTYPE(3'b101)
`define IS_REM `IS_MTYPE(3'b110)
`define IS_REMU `IS_MTYPE(3'b111)

`define IS_CSR (`INSTR[6:0] == 7'b1110011 && (|`INSTR[13:12]))
`define CSR_ADDR (`INSTR[31:20])

`define IS_ECALL (`INSTR == 32'b00000000000000000000000001110011)
`define IS_EBREAK (`INSTR == 32'b00000000000100000000000001110011)
`define IS_LUI (`INSTR[6:0] == 7'b0110111)
`define IS_BTYPE (`INSTR[6:0] == 7'b1100011 && (`INSTR[13] -> `INSTR[14]))
`define IS_MRET (`INSTR == 32'b00110000001000000000000001110011)
`define IS_WFI (`INSTR == 32'b00010000010100000000000001110011)

`define IS_CHERI_1(x) \
    (`INSTR[6:0] == 7'h5b && `INSTR[31:25] == 7'h7f && `INSTR[24:20] == x && `INSTR[14:12] == 3'h0)
`define IS_CHERI_2(x) (`INSTR[6:0] == 7'h5b && `INSTR[31:25] == x && `INSTR[14:12] == 3'h0)
`define IS_CHERI_3(x) (`INSTR[6:0] == 7'h5b && `INSTR[14:12] == x)
`define IS_CHERI_4(x) (`INSTR[6:0] == x)

`define IS_CGETPERM `IS_CHERI_1(5'h0)
`define IS_CGETTYPE `IS_CHERI_1(5'h1)
`define IS_CGETBASE `IS_CHERI_1(5'h2)
`define IS_CGETLEN `IS_CHERI_1(5'h3)
`define IS_CGETTAG `IS_CHERI_1(5'h4)
`define IS_CGETADDR `IS_CHERI_1(5'hf)
`define IS_CGETTOP `IS_CHERI_1(5'h18)

`define IS_CGET ( \
    `IS_CGETPERM | `IS_CGETTYPE | `IS_CGETBASE | `IS_CGETLEN | \
    `IS_CGETTAG | `IS_CGETADDR | `IS_CGETTOP \
)

`define IS_CSEAL `IS_CHERI_2(5'hb)
`define IS_CUNSEAL `IS_CHERI_2(5'hc)
`define IS_CANDPERM `IS_CHERI_2(5'hd)

`define IS_CSEAL_ANDPERM (`IS_CSEAL | `IS_CUNSEAL | `IS_CANDPERM)

`define IS_CSETADDR `IS_CHERI_2(5'h10)
`define IS_CINCADDR `IS_CHERI_2(5'h11)
`define IS_CINCADDRIMM `IS_CHERI_3(3'b001)

`define IS_CSETADDRx (`IS_CSETADDR | `IS_CINCADDR | `IS_CINCADDRIMM)

`define IS_CSETBOUNDS `IS_CHERI_2(5'h8)
`define IS_CSETBOUNDSEXACT `IS_CHERI_2(5'h9)
`define IS_CSETBOUNDSIMM `IS_CHERI_3(3'b010)
`define IS_CSETBOUNDSRNDN `IS_CHERI_2(5'b01010)
`define IS_CRRL `IS_CHERI_1(5'h8)
`define IS_CRAM `IS_CHERI_1(5'h9)

`define IS_CSETBOUNDSx ( \
    `IS_CSETBOUNDS | `IS_CSETBOUNDSEXACT | `IS_CSETBOUNDSIMM | `IS_CSETBOUNDSRNDN | \
    `IS_CRRL | `IS_CRAM \
)

`define IS_CCLEARTAG `IS_CHERI_1(5'hb)
`define IS_CSUB `IS_CHERI_2(7'h14)
`define IS_CMOVE `IS_CHERI_1(5'ha)
`define IS_CCLRSUBMOV (`IS_CCLEARTAG | `IS_CSUB | `IS_CMOVE)

`define IS_AUIPCC `IS_CHERI_4(7'h17)
`define IS_AUICGP `IS_CHERI_4(7'h7b)
`define IS_AUIC (`IS_AUIPCC | `IS_AUICGP)

`define IS_CTESTSUBSET `IS_CHERI_2(7'h20)
`define IS_CSEQX `IS_CHERI_2(7'h21)
`define IS_CCMP (`IS_CTESTSUBSET | `IS_CSEQX)

`define IS_CGETHIGH `IS_CHERI_1(5'h17)
`define IS_CSETHIGH `IS_CHERI_2(5'h16)
`define IS_CHIGH (`IS_CGETHIGH | `IS_CSETHIGH)

`define IS_CSPECIALRW `IS_CHERI_2(7'h1)

`define IS_CJAL (`INSTR[6:0] == 7'h6f)
`define IS_CJALR (`INSTR[6:0] == 7'h67 && `INSTR[14:12] == 3'b0)

`endif
