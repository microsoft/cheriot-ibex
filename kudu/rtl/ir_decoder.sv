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
 */


module ir_decoder import super_pkg::*; import cheri_pkg::*; #(
  parameter bit     CHERIoTEn  = 1'b0,
  parameter rv32m_e RV32M      = super_pkg::RV32MFast,
  parameter rv32b_e RV32B      = super_pkg::RV32BNone,
  parameter bit     IbexCmpt   = 1'b1 
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         cheri_pmode_i,
  input  logic         debug_mode_i,
  input  pcc_cap_t     pcc_cap_i,
  input  ir_reg_t      ir_reg_i,      // instruction read from memory/cache
  output ir_dec_t      ir_dec_o
);

  logic [31:0] instr;
  opcode_e     opcode;
  pl_type_e    pl_type;
  logic [4:0]  rs1, rs2, rd;
  logic [4:0]  reg_addr_mask;
  logic        rf_ren_a, rf_ren_b, rf_we;
  logic        rf_ren_a_final, rf_ren_b_final, rf_we_final;
  logic        illegal_insn, illegal_reg_cheri;
  logic        csr_insn, wfi_insn, ebrk_insn, ecall_insn, dret_insn, mret_insn, cjalr_insn;
  logic [31:0] imm_j_type, imm_b_type;
  logic        any_err;
  sysctl_t     sysctl;
  cheri_op_t   cheri_op;
  logic        cheri_opcode_en;
  logic        cheri_auipcc_en;
  logic        cheri_auicgp_en;
  logic        cheri_csc_en;
  logic        cheri_clc_en;
  logic        cheri_pmode;
  logic        cheri_perm_vio, cheri_bound_vio;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  assign instr = ir_reg_i.insn;

  assign opcode = opcode_e'(instr[6:0]);

  assign ir_dec_o.insn    = instr;
  assign ir_dec_o.pc      = ir_reg_i.pc;

  // QQQ let's worry about rs3 later
  // For rs1/rs2/rd and rf_ren*, rf_we, try to maintain compatiability with cheriot-ibex
  assign rs1              = cheri_auicgp_en ? 5'h3 : instr[19:15];
  assign rs2              = instr[24:20];
  assign rd               = instr[11:7];

  assign rf_ren_a_final   = IbexCmpt ? rf_ren_a & ~illegal_reg_cheri : rf_ren_a;
  assign rf_ren_b_final   = IbexCmpt ? rf_ren_b & ~illegal_reg_cheri : rf_ren_b;
  assign rf_we_final      = IbexCmpt ? rf_we & ~illegal_reg_cheri : rf_we;

  assign reg_addr_mask    = IbexCmpt ?  {~cheri_pmode, 4'hf} : 5'h1f;

  assign ir_dec_o.rs1     = (~IbexCmpt | rf_ren_a_final) ? (rs1 & reg_addr_mask) : 0;  
  assign ir_dec_o.rs2     = (~IbexCmpt | rf_ren_b_final) ? (rs2 & reg_addr_mask) : 0;
  assign ir_dec_o.rd      = (~IbexCmpt | rf_we_final)    ? (rd  & reg_addr_mask) : 0;

  assign ir_dec_o.pl_type = pl_type;
  assign ir_dec_o.rf_ren  = {rf_ren_b_final, rf_ren_a_final};
  assign ir_dec_o.rf_we   = rf_we_final;

  assign ir_dec_o.any_err = illegal_insn | illegal_reg_cheri | (|ir_reg_i.errs) | 
                            cheri_perm_vio | cheri_bound_vio;
  assign ir_dec_o.is_comp = ir_reg_i.is_comp;
  assign ir_dec_o.c_insn  = ir_reg_i.c_insn;

  assign ir_dec_o.errs.illegal_insn   = illegal_insn | illegal_reg_cheri;
  assign ir_dec_o.errs.perm_vio       = cheri_perm_vio;
  assign ir_dec_o.errs.bound_vio      = cheri_bound_vio;
  assign ir_dec_o.errs.illegal_c_insn = ir_reg_i.errs.illegal_c_insn;
  assign ir_dec_o.errs.fetch_err      = ir_reg_i.errs.fetch_err;

  assign ir_dec_o.is_branch = (opcode == OPCODE_BRANCH);
  assign ir_dec_o.is_jal    = (opcode == OPCODE_JAL);
  assign ir_dec_o.is_jalr   = (opcode == OPCODE_JALR);
  assign ir_dec_o.sysctl    = sysctl;
  assign ir_dec_o.is_cheri  = (opcode == OPCODE_JAL) || (opcode == OPCODE_JALR) || (|cheri_op);
  assign ir_dec_o.cheri_op  = cheri_op;

  assign ir_dec_o.ptaken  = ir_reg_i.ptaken;
  assign ir_dec_o.ptarget = ir_reg_i.ptarget;

  assign imm_j_type = { {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };
  assign imm_b_type = { {19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };

  assign ir_dec_o.btarget = ir_reg_i.pc + ((opcode == OPCODE_JAL) ? imm_j_type : imm_b_type);
  assign ir_dec_o.pc_nxt  = ir_reg_i.pc + (ir_reg_i.is_comp ? 2 : 4);
  
  assign sysctl.valid  = (csr_insn | wfi_insn | ebrk_insn | ecall_insn | dret_insn | 
                         mret_insn | cjalr_insn);
  assign sysctl.csr    = csr_insn;
  assign sysctl.mret   = mret_insn; 
  assign sysctl.dret   = dret_insn; 
  assign sysctl.wfi    = wfi_insn; 
  assign sysctl.ebrk   = ebrk_insn; 
  assign sysctl.ecall  = ecall_insn; 
  assign sysctl.cjalr  = cjalr_insn; 

  assign illegal_reg_cheri = cheri_pmode & ((rf_ren_a & rs1[4]) | (rf_ren_b & rs2[4]) | (rf_we & rd[4]));

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    pl_type             = PL_ALU;
    rf_ren_a            = 1'b0;
    rf_ren_b            = 1'b0;
    rf_we               = 1'b0;

    illegal_insn        = 1'b0;
    ebrk_insn           = 1'b0;
    mret_insn           = 1'b0;
    dret_insn           = 1'b0;
    ecall_insn          = 1'b0;
    wfi_insn            = 1'b0;
    csr_insn            = 1'b0;
    cjalr_insn          = 1'b0;
   
    cheri_opcode_en     = 1'b0; 
    cheri_auipcc_en     = 1'b0;
    cheri_auicgp_en     = 1'b0;
    cheri_clc_en        = 1'b0;
    cheri_csc_en        = 1'b0;

    unique case (opcode)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin   // Jump and Link
        pl_type       = PL_JAL;
        rf_we         = 1'b1;
      end

      OPCODE_JALR: begin  // Jump and Link Register
        pl_type       = PL_JALR;
        rf_ren_a      = 1'b1;
        rf_we         = 1'b1;
        illegal_insn  = (instr[14:12] != 3'b0);
        cjalr_insn    = cheri_pmode;
      end

      OPCODE_BRANCH: begin // Branch
        pl_type       = PL_BRANCH;
        rf_ren_a      = 1'b1;
        rf_ren_b      = 1'b1;
        illegal_insn  = (instr[14:13] == 2'b01);
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        pl_type       = PL_LS;
        rf_ren_a      = 1'b1;
        rf_ren_b      = 1'b1;
        cheri_csc_en  = cheri_pmode && (instr[14:12] == 3'b011);
        illegal_insn  = instr[14] | (~cheri_pmode && (instr[13:12] == 2'b11));
      end

      OPCODE_LOAD: begin
        pl_type       = PL_LS;
        rf_ren_a      = 1'b1;
        rf_we         = 1'b1;
        cheri_clc_en  = cheri_pmode && (instr[14:12] == 3'b011);
        illegal_insn  = (instr[14:13] == 2'b11) ||
                        & (~cheri_pmode && (instr[14:12] == 3'b011));
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        pl_type       = PL_ALU;
        rf_we         = 1'b1;
      end

      OPCODE_AUIPC: begin
        pl_type         = PL_ALU;
        rf_we           = 1'b1;
        cheri_auipcc_en = cheri_pmode;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        pl_type       = PL_ALU;
        rf_ren_a      = 1'b1;
        rf_we         = 1'b1;
        // illegal_insn  = (instr[14:12] == 3'b001) || (instr[14:12] == 3'b101); // QQQ RV32B
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        rf_ren_a      = 1'b1;
        rf_ren_b      = 1'b1;
        rf_we         = 1'b1;

        if ({instr[26], instr[13:12]} == {1'b1, 2'b01}) begin
          illegal_insn = 1'b1; // cmix / cmov / fsl / fsr
        end else begin
          unique case ({instr[31:25], instr[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000},
            {7'b010_0000, 3'b000},
            {7'b000_0000, 3'b010},
            {7'b000_0000, 3'b011},
            {7'b000_0000, 3'b100},
            {7'b000_0000, 3'b110},
            {7'b000_0000, 3'b111},
            {7'b000_0000, 3'b001},
            {7'b000_0000, 3'b101},
            {7'b010_0000, 3'b101}: 
            begin
              pl_type       = PL_ALU;
            end

            // RV32M instructions
            {7'b000_0001, 3'b000},    // mul
            {7'b000_0001, 3'b001},    // mulh
            {7'b000_0001, 3'b010},    // mulhsu
            {7'b000_0001, 3'b011},    // mulhu
            {7'b000_0001, 3'b100},    // div
            {7'b000_0001, 3'b101},    // divu
            {7'b000_0001, 3'b110},    // rem
            {7'b000_0001, 3'b111}:    // remu
            begin // mul
              pl_type       = PL_MULT;
              illegal_insn  = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            pl_type       = PL_BRANCH;
          end
          3'b001: begin
            // FENCE.I is implemented as a jump to the next PC, this gives the required flushing
            // behaviour (iside prefetch buffer flushed and response to any outstanding iside
            // requests will be ignored).
            // If present, the ICache will also be flushed.
            pl_type       = PL_BRANCH;
          end
          default: begin
            illegal_insn       = 1'b1;
          end
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr[14:12] == 3'b000) begin
          pl_type = PL_BRANCH;
          // non CSR related SYSTEM instructions
          unique case (instr[31:20])
            12'h000:  // ECALL
              // environment (system) call
              ecall_insn = 1'b1;

            12'h001:  // ebreak
              // debugger trap
              ebrk_insn = 1'b1;

            12'h302:  // mret
              mret_insn = 1'b1;

            12'h7b2:  // dret
              dret_insn = 1'b1;

            12'h105:  // wfi
              wfi_insn = 1'b1;

            default:
              illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (ir_dec_o.rs1 != 5'b0 || ir_dec_o.rd != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          // instruction to read/modify CSR
          csr_insn     = 1'b1;
          pl_type      = PL_MULT;
          rf_ren_a     = ~instr[14];
          rf_we        = 1'b1;
          illegal_insn = (instr[13:12] == 2'b00);
        end
      end

      OPCODE_CHERI: begin
        logic cheri_go_mult;
        cheri_go_mult   = cheri_op.cscrrw | cheri_op.csetbounds | cheri_op.csetboundsex |
                          cheri_op.csetboundsimm | cheri_op.csetboundsrndn | cheri_op.crrl | cheri_op.cram;
        pl_type         = cheri_go_mult ? PL_MULT : PL_ALU;   
        rf_ren_a        = 1'b1;
        rf_ren_b        = (instr[14:12] == 0) && (instr[31:25] != 7'h7f) && (instr[31:25] != 7'h01);
        rf_we           = 1'b1;
        cheri_opcode_en = 1'b1;
        illegal_insn    = ~cheri_pmode | ~(|cheri_op);
      end

      OPCODE_AUICGP: begin
        pl_type         = PL_ALU;
        rf_ren_a        = 1'b1;
        rf_ren_b        = 1'b0;
        rf_we           = 1'b1;
        cheri_auicgp_en = 1'b1;
        illegal_insn    = ~cheri_pmode;
      end

      default: begin
        illegal_insn = 1'b1;
      end
    endcase

  end

  //
  // CHERIoT instruction sub-decoding
  //

  logic [2:0] func3;
  logic [6:0] func7;
  logic [4:0] imm5;
  logic [4:0] rd_op;

  assign func3  = instr[14:12];
  assign func7  = instr[31:25];
  assign imm5   = instr[24:20];
  assign rd_op  = instr[11:7];

  assign cheri_op.cscrrw           = cheri_opcode_en && (func3==0) && (func7==7'h01);
  assign cheri_op.csetbounds       = cheri_opcode_en && (func3==0) && (func7==7'h08);
  assign cheri_op.csetboundsex     = cheri_opcode_en && (func3==0) && (func7==7'h09);
  assign cheri_op.csetboundsrndn   = cheri_opcode_en && (func3==0) && (func7==7'h0a);
  assign cheri_op.cseal            = cheri_opcode_en && (func3==0) && (func7==7'h0b);
  assign cheri_op.cunseal          = cheri_opcode_en && (func3==0) && (func7==7'h0c);
  assign cheri_op.candperm         = cheri_opcode_en && (func3==0) && (func7==7'h0d);
  assign cheri_op.csetaddr         = cheri_opcode_en && (func3==0) && (func7==7'h10);
  assign cheri_op.cincaddr         = cheri_opcode_en && (func3==0) && (func7==7'h11);
  assign cheri_op.csub             = cheri_opcode_en && (func3==0) && (func7==7'h14);
  assign cheri_op.csethigh         = cheri_opcode_en && (func3==0) && (func7==7'h16);
  assign cheri_op.ctestsub         = cheri_opcode_en && (func3==0) && (func7==7'h20);
  assign cheri_op.cseteqx          = cheri_opcode_en && (func3==0) && (func7==7'h21);
  
  assign cheri_op.cgetperm         = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h00);
  assign cheri_op.cgettype         = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h01);
  assign cheri_op.cgetbase         = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h02);
  assign cheri_op.cgethigh         = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h17);
  assign cheri_op.cgettop          = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h18);
  assign cheri_op.cgetlen          = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h03);
  assign cheri_op.cgettag          = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h04);
  assign cheri_op.crrl             = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h08);
  assign cheri_op.cram             = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h09);
  assign cheri_op.cgetaddr         = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h0f);
  assign cheri_op.cmove            = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h0a);
  assign cheri_op.ccleartag        = cheri_opcode_en && (func3==0) && (func7==7'h7f) && (imm5==5'h0b);
  
  assign cheri_op.cincaddrimm      = cheri_opcode_en && (func3 == 1);
  assign cheri_op.csetboundsimm    = cheri_opcode_en && (func3 == 2);
  
  assign cheri_op.auipcc           = cheri_auipcc_en;
  assign cheri_op.auicgp           = cheri_auicgp_en;
  assign cheri_op.clc              = cheri_clc_en;
  assign cheri_op.csc              = cheri_csc_en;

  //
  // CHERIoT fetch bounds check
  //

  logic [33:0] instr_hdrm;
  logic        hdrm_ge4, hdrm_ge2, hdrm_ok, base_ok;
  logic        allow_all;

  // allow_all is used to permit the pc wraparound case (pc = 0xffff_fffe, uncompressed instruction)
  // - in this case fetch should be allowed if pcc bounds is specified as the entire 32-bit space. 
  // - If we don't treat this as a specail case the fetch would be erred since headroom < 4
  assign allow_all  = (pcc_cap_i.base32==0) & (pcc_cap_i.top33[32]==1'b1);

  assign instr_hdrm = {1'b0, pcc_cap_i.top33} - {2'b00, ir_reg_i.pc};
  assign hdrm_ge4   = (|instr_hdrm[32:2]) & ~instr_hdrm[33];     // >= 4
  assign hdrm_ge2   = (|instr_hdrm[32:1]) & ~instr_hdrm[33];     // >= 2
  assign hdrm_ok    = allow_all || (ir_reg_i.is_comp ? hdrm_ge2 : hdrm_ge4);
  assign base_ok    = ~(ir_reg_i.pc < pcc_cap_i.base32);

  // only issue cheri_acc_vio on valid fetches
  assign cheri_bound_vio = cheri_pmode & ~debug_mode_i & (~base_ok | ~hdrm_ok);

  // we still check seal/perm here to be safe, however by ISA those can't happen at fetch time 
  // since they are check elsewhere already
  assign cheri_perm_vio = cheri_pmode & ~debug_mode_i &
                         (~pcc_cap_i.perms[PERM_EX] || ~pcc_cap_i.valid || (pcc_cap_i.otype!=0) ||
                          (mret_insn & ~pcc_cap_i.perms[PERM_SR]));

endmodule 
