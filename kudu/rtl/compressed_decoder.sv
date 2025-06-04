// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Compressed instruction decoder
 *
 * Decodes RISC-V compressed instructions into their RV32 equivalent.
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

module compressed_decoder import super_pkg::*;  # (
  parameter bit CHERIoTEn  = 1'b1
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        cheri_pmode_i,
  input  ir_reg_t     instr_i,
  output ir_reg_t     instr_o
);
  logic [15:0] insn16;
  logic [31:0] insn32;
  logic        illegal_c_insn;

  always_comb begin
    instr_o         = instr_i;   // pass through fields
    instr_o.insn    = insn32;
    instr_o.c_insn  = insn16;

    instr_o.errs.illegal_c_insn = illegal_c_insn;
  end

  ////////////////////////
  // Compressed decoder //
  ////////////////////////
  assign insn16 = instr_i.insn[15:0];

  always_comb begin
    // By default, forward incoming instruction, mark it as legal.
    insn32       = instr_i.insn;
    illegal_c_insn = 1'b0;

    // Check if incoming instruction is compressed.
    unique case (insn16[1:0])
      // C0
      2'b00: begin
        unique case (insn16[15:13])
          3'b000: begin
            if (CHERIoTEn & cheri_pmode_i)
              // c.incaddr4cspn -> cincoffsetimm cd', csp, imm
              insn32 = {2'b0, insn16[10:7], insn16[12:11], insn16[5],
                        insn16[6], 2'b00, 5'h02, 3'b001, 2'b01, insn16[4:2], {OPCODE_CHERI}};
            else
              // c.addi4spn -> addi rd', x2, imm
              insn32 = {2'b0, insn16[10:7], insn16[12:11], insn16[5],
                         insn16[6], 2'b00, 5'h02, 3'b000, 2'b01, insn16[4:2], {OPCODE_OP_IMM}};
            if (insn16[12:5] == 8'b0)  illegal_c_insn = 1'b1;
          end

          3'b010: begin
            // c.lw -> lw rd', imm(rs1')
            insn32 = {5'b0, insn16[5], insn16[12:10], insn16[6],
                       2'b00, 2'b01, insn16[9:7], 3'b010, 2'b01, insn16[4:2], {OPCODE_LOAD}};
          end

          3'b011: begin
            if (CHERIoTEn & cheri_pmode_i) begin
              // CHERI: c.clc -> clc rd', imm(rs1'); reuse c.ld
              insn32 = {4'b0, insn16[6:5], insn16[12:10],
                         3'b000, 2'b01, insn16[9:7], 3'b011, 2'b01, insn16[4:2], {OPCODE_LOAD}};
             end else begin
              insn32 = insn16;
              illegal_c_insn = 1'b1;
            end
          end

          3'b110: begin
            // c.sw -> sw rs2', imm(rs1')
            insn32 = {5'b0, insn16[5], insn16[12], 2'b01, insn16[4:2],
                       2'b01, insn16[9:7], 3'b010, insn16[11:10], insn16[6],
                       2'b00, {OPCODE_STORE}};
          end

          3'b001,
          3'b100,
          3'b101: begin
            illegal_c_insn = 1'b1;
          end

          3'b111: begin
            if (CHERIoTEn & cheri_pmode_i) begin
              // CHERI: c.csc -> csc rs2', imm(rs1'); reuse c.sd
              insn32 = {4'b0, insn16[6:5], insn16[12], 2'b01, insn16[4:2],
                         2'b01, insn16[9:7], 3'b011, insn16[11:10], 3'b000, {OPCODE_STORE}};
            end else begin
              insn32 = insn16;
              illegal_c_insn = 1'b1;
            end

          end

          default: begin
            illegal_c_insn = 1'b1;
          end
        endcase
      end

      // C1
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b01: begin
        unique case (insn16[15:13])
          3'b000: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop now maps to NOP in CHERIoT mode
            logic [4:0] rd_dec;
            logic [5:0] nzimm;
            nzimm   = {insn16[12], insn16[6:2]};
            rd_dec  = (CHERIoTEn & cheri_pmode_i && (nzimm == 6'h0)) ? 5'h0 : insn16[11:7];
            insn32 = {{6 {insn16[12]}}, insn16[12], insn16[6:2],
                       insn16[11:7], 3'b0, rd_dec, {OPCODE_OP_IMM}};
          end

          3'b001, 3'b101: begin
            // 001: c.jal -> jal x1, imm
            // 101: c.j   -> jal x0, imm
            insn32 = {insn16[12], insn16[8], insn16[10:9], insn16[6],
                       insn16[7], insn16[2], insn16[11], insn16[5:3],
                       {9 {insn16[12]}}, 4'b0, ~insn16[15], {OPCODE_JAL}};
          end

          3'b010: begin
            // c.li -> addi rd, x0, nzimm
            // (c.li hints are translated into an addi hint)
            insn32 = {{6 {insn16[12]}}, insn16[12], insn16[6:2], 5'b0,
                       3'b0, insn16[11:7], {OPCODE_OP_IMM}};
          end

          3'b011: begin
            // c.lui -> lui rd, imm
            // (c.lui hints are translated into a lui hint)
            insn32 = {{15 {insn16[12]}}, insn16[6:2], insn16[11:7], {OPCODE_LUI}};

            // c.incaddr16csp -> cincoffsetimm csp, csp, nzimm
            if (CHERIoTEn & cheri_pmode_i &&  (insn16[11:7] == 5'h02))  begin
              insn32 = {{3 {insn16[12]}}, insn16[4:3], insn16[5], insn16[2],
                         insn16[6], 4'b0, 5'h02, 3'b001,  5'h02, {OPCODE_CHERI}};
            end else if (insn16[11:7] == 5'h02)  begin
              // c.addi16sp -> addi x2, x2, nzimm
              insn32 = {{3 {insn16[12]}}, insn16[4:3], insn16[5], insn16[2],
                         insn16[6], 4'b0, 5'h02, 3'b000, 5'h02, {OPCODE_OP_IMM}};
            end

            if ({insn16[12], insn16[6:2]} == 6'b0) illegal_c_insn = 1'b1;
          end

          3'b100: begin
            unique case (insn16[11:10])
              2'b00,
              2'b01: begin
                // 00: c.srli -> srli rd, rd, shamt
                // 01: c.srai -> srai rd, rd, shamt
                // (c.srli/c.srai hints are translated into a srli/srai hint)
                insn32 = {1'b0, insn16[10], 5'b0, insn16[6:2], 2'b01, insn16[9:7],
                           3'b101, 2'b01, insn16[9:7], {OPCODE_OP_IMM}};
                if (insn16[12] == 1'b1)  illegal_c_insn = 1'b1;
              end

              2'b10: begin
                // c.andi -> andi rd, rd, imm
                insn32 = {{6 {insn16[12]}}, insn16[12], insn16[6:2], 2'b01, insn16[9:7],
                           3'b111, 2'b01, insn16[9:7], {OPCODE_OP_IMM}};
              end

              2'b11: begin
                unique case ({insn16[12], insn16[6:5]})
                  3'b000: begin
                    // c.sub -> sub rd', rd', rs2'
                    insn32 = {2'b01, 5'b0, 2'b01, insn16[4:2], 2'b01, insn16[9:7],
                               3'b000, 2'b01, insn16[9:7], {OPCODE_OP}};
                  end

                  3'b001: begin
                    // c.xor -> xor rd', rd', rs2'
                    insn32 = {7'b0, 2'b01, insn16[4:2], 2'b01, insn16[9:7], 3'b100,
                               2'b01, insn16[9:7], {OPCODE_OP}};
                  end

                  3'b010: begin
                    // c.or  -> or  rd', rd', rs2'
                    insn32 = {7'b0, 2'b01, insn16[4:2], 2'b01, insn16[9:7], 3'b110,
                               2'b01, insn16[9:7], {OPCODE_OP}};
                  end

                  3'b011: begin
                    // c.and -> and rd', rd', rs2'
                    insn32 = {7'b0, 2'b01, insn16[4:2], 2'b01, insn16[9:7], 3'b111,
                               2'b01, insn16[9:7], {OPCODE_OP}};
                  end

                  3'b100,
                  3'b101,
                  3'b110,
                  3'b111: begin
                    // 100: c.subw
                    // 101: c.addw
                    illegal_c_insn = 1'b1;
                  end

                  default: begin
                    illegal_c_insn = 1'b1;
                  end
                endcase
              end

              default: begin
                illegal_c_insn = 1'b1;
              end
            endcase
          end

          3'b110, 3'b111: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            insn32 = {{4 {insn16[12]}}, insn16[6:5], insn16[2], 5'b0, 2'b01,
                       insn16[9:7], 2'b00, insn16[13], insn16[11:10], insn16[4:3],
                       insn16[12], {OPCODE_BRANCH}};
          end

          default: begin
            illegal_c_insn = 1'b1;
          end
        endcase
      end

      // C2
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b10: begin
        unique case (insn16[15:13])
          3'b000: begin
            // c.slli -> slli rd, rd, shamt
            // (c.ssli hints are translated into a slli hint)
            insn32 = {7'b0, insn16[6:2], insn16[11:7], 3'b001, insn16[11:7], {OPCODE_OP_IMM}};
            if (insn16[12] == 1'b1)  illegal_c_insn = 1'b1; // reserved for custom extensions
          end

          3'b010: begin
            // c.lwsp -> lw rd, imm(x2)
            insn32 = {4'b0, insn16[3:2], insn16[12], insn16[6:4], 2'b00, 5'h02,
                       3'b010, insn16[11:7], OPCODE_LOAD};
            if (insn16[11:7] == 5'b0)  illegal_c_insn = 1'b1;
          end

          3'b011: begin
            if (CHERIoTEn & cheri_pmode_i) begin
              // c.clcsp -> clc cd, imm(c2),  reused c.ldsp
              insn32 = {3'b0, insn16[4:2], insn16[12], insn16[6:5], 3'b000, 5'h02,
                         3'b011, insn16[11:7], OPCODE_LOAD};
              if (insn16[11:7] == 5'b0)  illegal_c_insn = 1'b1;
            end else begin
              insn32 = insn16;
              illegal_c_insn = 1'b1;
            end 
          end

          3'b100: begin
            if (insn16[12] == 1'b0) begin
              if (insn16[6:2] != 5'b0) begin
                // c.mv -> add rd/rs1, x0, rs2
                // (c.mv hints are translated into an add hint)
                insn32 = {7'b0, insn16[6:2], 5'b0, 3'b0, insn16[11:7], {OPCODE_OP}};
              end else begin
                // c.jr -> jalr x0, rd/rs1, 0
                insn32 = {12'b0, insn16[11:7], 3'b0, 5'b0, {OPCODE_JALR}};
                if (insn16[11:7] == 5'b0) illegal_c_insn = 1'b1;
              end
            end else begin
              if (insn16[6:2] != 5'b0) begin
                // c.add -> add rd, rd, rs2
                // (c.add hints are translated into an add hint)
                insn32 = {7'b0, insn16[6:2], insn16[11:7], 3'b0, insn16[11:7], {OPCODE_OP}};
              end else begin
                if (insn16[11:7] == 5'b0) begin
                  // c.ebreak -> ebreak
                  insn32 = {32'h00_10_00_73};
                end else begin
                  // c.jalr -> jalr x1, rs1, 0
                  insn32 = {12'b0, insn16[11:7], 3'b000, 5'b00001, {OPCODE_JALR}};
                end
              end
            end
          end

          3'b110: begin
            // c.swsp -> sw rs2, imm(x2)
            insn32 = {4'b0, insn16[8:7], insn16[12], insn16[6:2], 5'h02, 3'b010,
                       insn16[11:9], 2'b00, {OPCODE_STORE}};
          end

          3'b111: begin
            if (CHERIoTEn & cheri_pmode_i) begin
              // c.cscsp -> csc cs2, imm(c2),  reuse c.sdsp
              insn32 = {3'b0, insn16[9:7], insn16[12], insn16[6:2], 5'h02, 3'b011,
                         insn16[11:10], 3'b000, {OPCODE_STORE}};
            end else begin 
              insn32 = insn16;
              illegal_c_insn = 1'b1;
            end
          end


          3'b001,
          3'b101: begin
            illegal_c_insn = 1'b1;
          end

          default: begin
            illegal_c_insn = 1'b1;
          end
        endcase
      end

      // Incoming instruction is not compressed.
      2'b11:;

      default: begin
        illegal_c_insn = 1'b1;
      end
    endcase
  end

endmodule
