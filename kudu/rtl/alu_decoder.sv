// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Instruction decoder
 *
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

module alu_decoder import super_pkg::*; #(
  parameter bit CHERIoTEn           = 1'b1
) (
  input  ir_dec_t         instr_i,               // instruction read from memory/cache
  input  logic            cheri_pmode_i,
  output logic [31:0]     imm_o,                 
  output alu_op_e         alu_operator_o,        // ALU operation selection
  output op_a_sel_e       alu_op_a_mux_sel_o,    // operand a selection: reg value, PC, immediate or zero
  output op_b_sel_e       alu_op_b_mux_sel_o     // operand b selection: reg value or immediate
);

  logic [31:0] instr_alu;

  opcode_e     opcode_alu;

  imm_b_sel_e  imm_mux_sel;       // immediate selection for operand b
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;
  logic [31:0] imm_c20_type;

  // To help timing the flops containing the current instruction are replicated to reduce fan-out.
  // instr_alu is used to determine the ALU control logic and associated operand/imm select signals
  // as the ALU is often on the more critical timing paths. instr is used for everything else.
  assign instr_alu = instr_i.insn;

  //////////////////////////////////////
  // Register and immediate selection //
  //////////////////////////////////////

  // immediate extraction and sign extension
  
  assign imm_c20_type = { instr_alu[31],  instr_alu[31:12], 11'h0 };  // AUIPCC CHERIoT
  assign imm_i_type   = { {20{instr_alu[31]}}, instr_alu[31:20] };
  assign imm_s_type   = { {20{instr_alu[31]}}, instr_alu[31:25], instr_alu[11:7] };
  assign imm_b_type   = { {19{instr_alu[31]}}, instr_alu[31], instr_alu[7], instr_alu[30:25], instr_alu[11:8], 1'b0 };
  assign imm_u_type   = { instr_alu[31:12], 12'b0 };
  assign imm_j_type   = { {12{instr_alu[31]}}, instr_alu[19:12], instr_alu[20], instr_alu[30:21], 1'b0 };

  // immediate for CSR manipulation (zero extended)
  assign zimm_rs1_type = { 27'b0, instr_alu[19:15] }; // rs1

  // mux the imm output
  always_comb begin : immediate_mux
    unique case (imm_mux_sel)
      IMM_B_I:         imm_o = imm_i_type;
      IMM_B_S:         imm_o = imm_s_type;
      IMM_B_U:         imm_o = imm_u_type;
      IMM_B_INCR_PC:   imm_o = instr_i.is_comp ? 32'h2 : 32'h4;
      IMM_B_C20:       imm_o = imm_c20_type;
      default:         imm_o = 32'h4;
    endcase
  end

  /////////////////////////////
  // Decoder for ALU control //
  /////////////////////////////

  always_comb begin
    alu_operator_o     = ALU_SLTU;
    alu_op_a_mux_sel_o = OP_A_IMM;
    alu_op_b_mux_sel_o = OP_B_IMM;

    imm_mux_sel      = IMM_B_I;

    opcode_alu         = opcode_e'(instr_alu[6:0]);

    unique case (opcode_alu)
      /////////
      // ALU //
      /////////

      OPCODE_JAL, OPCODE_JALR: begin  // pass through
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;      // same between RV32 and CHERIoT
        imm_mux_sel         = IMM_B_INCR_PC;
        alu_operator_o      = ALU_ADD;
      end
      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_mux_sel         = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      // use CHERI version of AUIPCC when pmode == 1
      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_mux_sel         = (CHERIoTEn & cheri_pmode_i) ? IMM_B_C20 : IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_mux_sel       = IMM_B_I;

        unique case (instr_alu[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLT;  // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator_o = ALU_SLL; // Shift Left Logical by Immediate
          end

          3'b101: begin
            if (instr_alu[31:27] == 5'b0_0000) begin
              alu_operator_o = ALU_SRL;               // Shift Right Logical by Immediate
            end else if (instr_alu[31:27] == 5'b0_1000) begin
              alu_operator_o = ALU_SRA;               // Shift Right Arithmetically by Immediate
            end
          end

          default: ;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;

        unique case ({instr_alu[31:25], instr_alu[14:12]})
          // RV32I ALU operations
          {7'b000_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
          {7'b010_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
          {7'b000_0000, 3'b010}: alu_operator_o = ALU_SLT;   // Set Lower Than
          {7'b000_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
          {7'b000_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
          {7'b000_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
          {7'b000_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
          {7'b000_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
          {7'b000_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
          {7'b010_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

          default: ;
        endcase
      end

      OPCODE_CHERI: begin
        // only handle cincaddr, cincaddrimm, csub here
        alu_op_a_mux_sel_o = OP_A_REG_A;
        imm_mux_sel        = IMM_B_I;

        if (instr_i.cheri_op.csub)
          alu_operator_o     = ALU_SUB;
        else 
          alu_operator_o     = ALU_ADD;
        
        if (instr_i.cheri_op.cincaddr | instr_i.cheri_op.csub)
          alu_op_b_mux_sel_o = OP_B_REG_B;
        else if (instr_i.cheri_op.cincaddrimm)
          alu_op_b_mux_sel_o = OP_B_IMM;

      end

      OPCODE_AUICGP: begin
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_IMM;
        imm_mux_sel        = IMM_B_C20;
        alu_operator_o     = ALU_ADD;
      end

      default : ;
    endcase
  end

endmodule // alu_decoder
