// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
//  CHERIoT ALU (single cycle instructions)
// 

module cheri_alu import super_pkg::*; import cheri_pkg::*; (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  logic              debug_mode_i,
  input  logic              alu_en_i,

  input  ir_dec_t           instr_i,
  input  full_data2_t       full_data2_i,
  input  logic [31:0]       rv32_alu_result_i,
  input  pcc_cap_t          pcc_cap_i,
  input  logic              csr_mstatus_mie_i,
  output op_cap_t           result_ocap_o
);

  // bounds check for cseal/cunseal  QQQ check with Robert N 
  function automatic logic check_bounds (full_cap_t cs2_fcap, logic [3:0] chkaddr);
    logic result;
      result  = ((cs2_fcap.top33[3:0] <= chkaddr) && (cs2_fcap.top33[32:4] == 0)) ||
                ((cs2_fcap.base32[3:0] > chkaddr[3:0]) || (cs2_fcap.base32[31:4] != 0));
    return result;
  endfunction

  full_cap_t   cs1_fcap, cs2_fcap;
  full_cap_t   imd_fcap, imd_fcap_q, final_fcap;
  logic        bound_vio, perm_vio;
  logic        setaddr_flag, setaddr_flag_q;
  logic [8:0]  ptrmi9, ptrmi9_q;

  assign cs1_fcap = full_cap_t'(full_data2_i.d0);
  assign cs2_fcap = full_cap_t'(full_data2_i.d1);

  assign final_fcap    = setaddr_flag_q ? set_address_lite(imd_fcap_q, ptrmi9_q) : imd_fcap_q;
  assign result_ocap_o = op_cap_t'(final_fcap);

  // 
  // CHERI ALU instruction EX
  //

  always_comb begin : cheri_ex
    imd_fcap     = NULL_FULL_CAP;
    perm_vio     = 1'b0;
    bound_vio    = 1'b0;
    setaddr_flag = 1'b0;
    ptrmi9       = 9'h0;

    unique case (1'b1) 
      instr_i.cheri_op.cgetperm : 
        imd_fcap.addr = cs1_fcap.perms;

      instr_i.cheri_op.cgettype : 
        imd_fcap.addr = {28'h0, decode_otype(cs1_fcap.otype, cs1_fcap.perms[PERM_EX])};

      instr_i.cheri_op.cgetbase : 
        imd_fcap.addr = cs1_fcap.base32;

      instr_i.cheri_op.cgettop : 
        imd_fcap.addr = cs1_fcap.top33[32] ? 32'hffff_ffff : cs1_fcap.top33[31:0];

      instr_i.cheri_op.cgetlen : 
        imd_fcap.addr = get_cap_len(cs1_fcap);   // QQQ should use rv32alu 

      instr_i.cheri_op.cgettag : 
        imd_fcap.addr = {31'h0, cs1_fcap.valid};

      instr_i.cheri_op.cgetaddr : 
        imd_fcap.addr = cs1_fcap.addr;

      instr_i.cheri_op.cgethigh:
        begin
          logic [MemW-1:0] tmp_mem_cap;
          tmp_mem_cap   = op2memcap(cs1_fcap[OpW-1:0]);
          imd_fcap.addr = tmp_mem_cap[63:32];
        end

      instr_i.cheri_op.cseal :
        begin
          logic       cs2_bad_type;
          logic [3:0] chkaddr;
          chkaddr        = cs2_fcap.addr[3:0];
          // cs2.addr check : ex: 0-7, non-ex: 9-15
          cs2_bad_type   = cs1_fcap.perms[PERM_EX] ? ((cs2_fcap.addr[31:3]!=0) || (cs2_fcap.addr[2:0]==0)) :
                                                   ((|cs2_fcap.addr[31:4]) || (cs2_fcap.addr[3:0] <= 8));
          perm_vio       = ~cs2_fcap.valid | is_cap_sealed(cs1_fcap) | is_cap_sealed(cs2_fcap) |
                           ~cs2_fcap.perms[PERM_SE] | cs2_bad_type;
          bound_vio      = check_bounds(cs2_fcap, chkaddr);
          imd_fcap       = cs1_fcap;
          imd_fcap.otype = cs2_fcap.addr[OTYPE_W-1:0];
          imd_fcap.valid = cs1_fcap.valid & (~perm_vio) & (~bound_vio);
        end

      instr_i.cheri_op.cunseal :
        begin
          logic [3:0] chkaddr;
          chkaddr   = decode_otype(cs1_fcap.otype, cs1_fcap.perms[PERM_EX]);
          bound_vio = check_bounds(cs2_fcap, chkaddr);
          perm_vio  = ~cs2_fcap.valid | (~is_cap_sealed(cs1_fcap)) | is_cap_sealed(cs2_fcap) |
                       (~cs2_fcap.perms[PERM_US]);    
          imd_fcap                = cs1_fcap;
          imd_fcap.otype          = OTYPE_UNSEALED;
          imd_fcap.perms[PERM_GL] = cs1_fcap.perms[PERM_GL] & cs2_fcap.perms[PERM_GL];
          imd_fcap.cperms         = compress_perms(imd_fcap.perms, cs1_fcap.cperms[5:4]);
          imd_fcap.valid          = cs1_fcap.valid & (~perm_vio) & (~bound_vio);
        end
   
      instr_i.cheri_op.candperm :
        begin
          logic [PERMS_W-1:0] pmask;
          pmask           = cs2_fcap.addr[PERMS_W-1:0];
          pmask[PERM_GL]  = 1'b1;
          imd_fcap        = cs1_fcap;
          imd_fcap.perms  = cs1_fcap.perms & cs2_fcap.addr[PERMS_W-1:0];
          imd_fcap.cperms = compress_perms(imd_fcap.perms, cs1_fcap.cperms[5:4]);
          // for sealed caps, clear tag unless perm mask (excluding GL) == all '1'
          imd_fcap.valid  = cs1_fcap.valid & (~is_cap_sealed(cs1_fcap) | (&pmask));
        end

      instr_i.cheri_op.cincaddr, instr_i.cheri_op.csetaddr, instr_i.cheri_op.cincaddrimm,
      instr_i.cheri_op.auipcc, instr_i.cheri_op.auicgp :
        begin
          logic        clr_sealed;
          logic [31:0] new_addr;
          full_cap_t   tfcap, pfcap;
          
          // QQQ add clear-tag-escalate-to-fault feature later
          // QQQ shift things around for timing later
          clr_sealed     = instr_i.cheri_op.auipcc ? 1'b0 : is_cap_sealed(cs1_fcap);
          new_addr       = instr_i.cheri_op.csetaddr ? cs2_fcap.addr : rv32_alu_result_i;
          pfcap          = pcc2fullcap_lite(pcc_cap_i, instr_i.pc);
          tfcap          = instr_i.cheri_op.auipcc ? pfcap : cs1_fcap;
          imd_fcap       = tfcap;
          imd_fcap.addr  = new_addr;     
          imd_fcap.valid = imd_fcap.valid & ~clr_sealed;
          ptrmi9         = new_addr >> imd_fcap.exp;
          setaddr_flag   = 1'b1;
        end

      instr_i.cheri_op.ccleartag :
        begin
          imd_fcap       = cs1_fcap;
          imd_fcap.valid = 1'b0;
        end

      instr_i.cheri_op.ctestsub :
        imd_fcap.addr[0] = (cs1_fcap.valid  == cs2_fcap.valid) &&  
                           ~((cs2_fcap.base32 < cs1_fcap.base32) || (cs2_fcap.top33 > cs1_fcap.top33)) &&
                           (&(cs1_fcap.perms | ~cs2_fcap.perms));
       
      instr_i.cheri_op.cseteqx :
        imd_fcap.addr[0] = (cs1_fcap[MemW-1:0] == cs2_fcap[MemW-1:0]);

      instr_i.cheri_op.csethigh :
        imd_fcap[RegW-1:0] = mem2regcap({1'b0, cs2_fcap.addr, cs1_fcap.addr}, 4'h0);

      instr_i.cheri_op.csub :
        imd_fcap.addr = rv32_alu_result_i;

      instr_i.cheri_op.cmove:
        imd_fcap = cs1_fcap;

      instr_i.is_jal :       // CJALR is handled separately by mult_pl
        begin 
          logic [2:0] seal_type;         
          seal_type       = csr_mstatus_mie_i ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD;
          imd_fcap        = pcc2fullcap_lite(pcc_cap_i, rv32_alu_result_i);
          imd_fcap.otype  = (instr_i.rd == 5'h1) ? seal_type : imd_fcap.otype;
          ptrmi9          = rv32_alu_result_i >> imd_fcap.exp;
          setaddr_flag    = 1'b1;
        end
      default: ;
    endcase

  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      imd_fcap_q     <= NULL_FULL_CAP;
      setaddr_flag_q <= 1'b0;
      ptrmi9_q       <= 9'h0;
    end else if (alu_en_i) begin
      imd_fcap_q     <= imd_fcap;
      setaddr_flag_q <= setaddr_flag;
      ptrmi9_q       <= ptrmi9;
    end
  end

endmodule
