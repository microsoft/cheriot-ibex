// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module branch_unit import super_pkg::*; import cheri_pkg::*; #(
  parameter bit CHERIoTEn = 1'b1
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  logic          cheri_pmode_i,

  // IF/IR interface
  input  ir_dec_t       ira_dec_i,
  input  ir_dec_t       irb_dec_i,      
  input                 ira_is0_i,
 
  // Issuer interface
  input  logic [1:0]    branch_valid_i,
  input  full_data2_t   ira_full_data2_i,
  input  full_data2_t   irb_full_data2_i,

  output branch_info_t  branch_info_o,
  output logic [31:0]   ir0_jalr_target_o,
  output logic [31:0]   ir1_jalr_target_o,
  output logic [2:0]    ir0_cjalr_err_o,
  output logic [2:0]    ir1_cjalr_err_o
);

 
  function automatic logic branch_decision (ir_dec_t ir_dec, full_data2_t full_data2);
    logic        result;
    logic [31:0] a, b;
    logic        branch_go;
    logic        beq_flag, blt_flag, bltu_flag;
    logic [2:0]  func3;

    // a     = (ir_dec.rs1 != 0) ? rf_rdata2.d0 : 0;
    // b     = (ir_dec.rs2 != 0) ? rf_rdata2.d1 : 0;
    a     = full_data2.d0[31:0];
    b     = full_data2.d1[31:0];

    beq_flag  = (a == b);
    blt_flag  = ($signed (a) < $signed(b));
    bltu_flag = (a < b);

    func3     = ir_dec.insn[14:12];

    case (func3[2:1])
      2'b00: branch_go = beq_flag ^ func3[0];
      2'b10: branch_go = blt_flag ^ func3[0]; 
      2'b11: branch_go = bltu_flag ^ func3[0]; 
      default: branch_go = 1'b0;
    endcase

    result  = ir_dec.is_jal | (ir_dec.is_branch & branch_go);

    return result;
  endfunction

  function automatic logic [31:0] compute_jalr_target (ir_dec_t ir_dec, full_data2_t full_data2);
    logic [31:0] result;
    logic [31:0] imm_i_type;

    imm_i_type = { {20{ir_dec.insn[31]}}, ir_dec.insn[31:20] };
    result = full_data2.d0[31:0] + imm_i_type;
   
    return result;
  endfunction 

  function automatic logic [1:0] get_mispredict_type (ir_dec_t ir_dec, logic branch_taken);
    logic [1:0] result;  // bit 0: mispredict_taken, bit 1: mispredict_not_taken;

    // note it's possible in JAL case to have predict_taken == 0, since the jtb table
    // entry might be invalid
    if ((ir_dec.is_branch | ir_dec.is_jal) && ~ir_dec.ptaken & branch_taken)
      result[0] = 1'b1; 
    else if ((ir_dec.is_branch | ir_dec.is_jal) && ir_dec.ptaken && 
              branch_taken && (ir_dec.ptarget != ir_dec.btarget))
      result[0] = 1'b1; 
    else 
      result[0] = 1'b0; 

    result[1] = ir_dec.is_branch && ir_dec.ptaken & ~branch_taken;
  
    return result;
  endfunction

  function automatic logic [2:0] get_cjalr_err (ir_dec_t ir_dec, full_cap_t cs1_fcap);
    logic [2:0]  result;
    logic        cs1_otype_0, cs1_otype_1, cs1_otype_45, cs1_otype_23;
    logic [11:0] cheri_imm12;
   
    
    // otype_1: forward sentry; otype_23: forward inherit sentry; otype_45: backward sentry;
    cs1_otype_0  = (cs1_fcap.otype == 3'h0);
    cs1_otype_1  = cs1_fcap.perms[PERM_EX] & (cs1_fcap.otype == 3'h1);  // fwd sentry
    cs1_otype_23 = cs1_fcap.perms[PERM_EX] & ((cs1_fcap.otype == 3'h2) || (cs1_fcap.otype == 3'h3));
    cs1_otype_45 = cs1_fcap.perms[PERM_EX] & ((cs1_fcap.otype == 3'h4) || (cs1_fcap.otype == 3'h5));

    cheri_imm12 = ir_dec.insn[31:20];

    if (ir_dec.is_jalr) begin
      // PVIO_TAG
      result[0] = ~cs1_fcap.valid;     
      // PVIO_SEAL
      result[1] = (is_cap_sealed(cs1_fcap) && (cheri_imm12 != 0)) ||
                  ~(((ir_dec.rd == 0) && (ir_dec.rs1 == 5'h1) && cs1_otype_45) ||
                    ((ir_dec.rd == 0) && (ir_dec.rs1 != 5'h1) && (cs1_otype_0 || cs1_otype_1)) ||
                    ((ir_dec.rd == 5'h1) && (cs1_otype_0 | cs1_otype_23)) ||
                    ((ir_dec.rd != 0) && (cs1_otype_0 | cs1_otype_1)));
      // PVIO_EX
      result[2] = ~cs1_fcap.perms[PERM_EX];
    end else begin
      result = 3'h0;
    end

    return result;
  endfunction
  //
  // Branch decision
  //
  logic        branch_taken_a, branch_taken_b;
  logic [31:0] jalr_target_a, jalr_target_b;
  logic [2:0]  cjalr_err_a, cjalr_err_b;
  logic [1:0]  branch_taken_ordered;

  assign branch_taken_a = branch_decision(ira_dec_i, ira_full_data2_i);
  assign branch_taken_b = branch_decision(irb_dec_i, irb_full_data2_i);

  assign branch_taken_ordered = ira_is0_i ? {branch_taken_b,  branch_taken_a} : 
                                            {branch_taken_a,  branch_taken_b};

  assign branch_info_o.branch_taken = branch_taken_ordered;

  // Misprediction decision

  logic [1:0] tmpa, tmpb;

  assign tmpa = get_mispredict_type(ira_dec_i, branch_taken_a);
  assign tmpb = get_mispredict_type(irb_dec_i, branch_taken_b);

  assign branch_info_o.mispredict_taken     = ira_is0_i ? {tmpb[0], tmpa[0]} : {tmpa[0], tmpb[0]};
  assign branch_info_o.mispredict_not_taken = ira_is0_i ? {tmpb[1], tmpa[1]} : {tmpa[1], tmpb[1]};

  //
  // Compute JALR target addresses (based on resolved operands)
  
  assign jalr_target_a = compute_jalr_target(ira_dec_i, ira_full_data2_i);
  assign jalr_target_b = compute_jalr_target(irb_dec_i, irb_full_data2_i);

  if (CHERIoTEn) begin
    assign cjalr_err_a = cheri_pmode_i ? get_cjalr_err (ira_dec_i, ira_full_data2_i.d0) : 3'h0;
    assign cjalr_err_b = cheri_pmode_i ? get_cjalr_err (irb_dec_i, irb_full_data2_i.d0) : 3'h0;
  end else begin
    assign cjalr_err_a = 3'h0;
    assign cjalr_err_b = 3'h0;
  end 

  assign ir0_jalr_target_o = ira_is0_i ?  jalr_target_a : jalr_target_b;
  assign ir1_jalr_target_o = ira_is0_i ?  jalr_target_b : jalr_target_a;

  assign ir0_cjalr_err_o = ira_is0_i ? cjalr_err_a : cjalr_err_b;
  assign ir1_cjalr_err_o = ira_is0_i ? cjalr_err_b : cjalr_err_a;

  //
  // for simulation debugging only
  //
  full_cap_t ir0_cs1_fcap, ir0_cs2_fcap, ir1_cs1_fcap, ir1_cs2_fcap;
  assign ir0_cs1_fcap = ira_is0_i ? ira_full_data2_i.d0 : irb_full_data2_i.d0;
  assign ir0_cs2_fcap = ira_is0_i ? ira_full_data2_i.d1 : irb_full_data2_i.d1;
  assign ir1_cs1_fcap = ~ira_is0_i ? ira_full_data2_i.d0 : irb_full_data2_i.d0;
  assign ir1_cs2_fcap = ~ira_is0_i ? ira_full_data2_i.d1 : irb_full_data2_i.d1;
 

endmodule
