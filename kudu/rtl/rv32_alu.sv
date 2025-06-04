// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Arithmetic logic unit
 */
module rv32_alu import super_pkg::*; (
  input  alu_op_e      operator_i,
  input  op_a_sel_e    alu_op_a_mux_sel_i,
  input  op_b_sel_e    alu_op_b_mux_sel_i,
  input  logic[31:0]   rf_rdata_a_i,
  input  logic[31:0]   rf_rdata_b_i,
  input  logic[31:0]   pc_i,
  input  logic[31:0]   imm_i,
  output logic [31:0]  result_o
);

  logic [31:0]  operand_a;
  logic [31:0]  operand_b;

  logic [31:0] operand_a_rev;
  logic [32:0] operand_b_neg;

  //
  // ALU operand MUX
  //
  assign operand_a = (alu_op_a_mux_sel_i == OP_A_REG_A) ? rf_rdata_a_i :
                     ((alu_op_a_mux_sel_i == OP_A_CURRPC) ?  pc_i : 32'h0);
  assign operand_b = (alu_op_b_mux_sel_i == OP_B_IMM) ? imm_i : rf_rdata_b_i;

  // bit reverse operand_a for left shifts and bit counting
  for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
    assign operand_a_rev[k] = operand_a[31-k];
  end

  ///////////
  // Adder //
  ///////////

  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;
  logic [33:0] adder_result_ext;

  always_comb begin
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      ALU_SUB,

      // Comparator OPs
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU : adder_op_b_negate = 1'b1;

      default:;
    endcase
  end

  // prepare operand a
  assign adder_in_a = {operand_a,1'b1};

  // prepare operand b
  assign operand_b_neg = {operand_b,1'b0} ^ {33{1'b1}};
  always_comb begin
    unique case (1'b1)
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default:           adder_in_b = {operand_b, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result     = adder_result_ext[32:1];

  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      ALU_GE,
      ALU_LT,
      ALU_SLT: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);

  // Is greater equal
  always_comb begin
    if ((operand_a[31] ^ operand_b[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a[31] ^ (cmp_signed);
    end
  end

  // GTE unsigned:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1

  // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      ALU_EQ:             cmp_result =  is_equal;
      ALU_NE:             cmp_result = ~is_equal;
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  ///////////
  // Shift //
  ///////////

  logic       shift_left;
  logic       shift_ones;
  logic       shift_arith;
  logic [5:0] shift_amt;

  logic        [31:0] shift_operand;
  logic signed [32:0] shift_result_ext_signed;
  logic        [32:0] shift_result_ext;
  logic               unused_shift_result_ext;
  logic        [31:0] shift_result;
  logic        [31:0] shift_result_rev;

  // bit shift_amt[5]: word swap bit: only considered for FSL/FSR.
  // if set, reverse operations in first and second cycle.
  assign shift_amt[5] = 1'b0;
  assign shift_amt[4:0] = operand_b[4:0];

  always_comb begin
    unique case (operator_i)
      ALU_SLL: shift_left = 1'b1;
      default: shift_left = 1'b0;
    endcase
  end

  assign shift_arith  = (operator_i == ALU_SRA);
  assign shift_ones   = 1'b0;

  // shifter structure.
  assign  shift_operand = shift_left ? operand_a_rev : operand_a;
  always_comb begin

    shift_result_ext_signed =
        $signed({(shift_arith & shift_operand[31]), shift_operand}) >>> shift_amt[4:0];
    shift_result_ext = $unsigned(shift_result_ext_signed);

    shift_result            = shift_result_ext[31:0];
    unused_shift_result_ext = shift_result_ext[32];

    for (int unsigned i = 0; i < 32; i++) begin
      shift_result_rev[i] = shift_result[31-i];
    end

    shift_result = shift_left ? shift_result_rev : shift_result;

  end

  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;
  logic [31:0] bwlogic_result;

  logic bwlogic_op_b_negate;

  assign  bwlogic_op_b_negate = 1'b0;

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b;

  assign bwlogic_or_result  = operand_a | bwlogic_operand_b;
  assign bwlogic_and_result = operand_a & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR);
  assign bwlogic_and = (operator_i == ALU_AND);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end


  ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B)
      ALU_XOR, ALU_OR, ALU_AND: result_o = bwlogic_result;

      // Adder Operations
      ALU_ADD,  ALU_SUB: result_o = adder_result;

      // Shift Operations
      ALU_SLL,  ALU_SRL,
      ALU_SRA: result_o = shift_result;

      // Comparison Operations
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: result_o = {31'h0,cmp_result};

      default: ;
    endcase
  end

endmodule
