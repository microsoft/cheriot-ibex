// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cheri_pkg;

  // bit field widths
  parameter int unsigned ADDR_W    = 32;
  parameter int unsigned TOP_W     = 9;
  parameter int unsigned BOT_W     = 9;
  parameter int unsigned CEXP_W    = 4;
  parameter int unsigned EXP_W     = 5;
  parameter int unsigned OTYPE_W   = 3;
  parameter int unsigned CPERMS_W  = 7;
  parameter int unsigned PERMS_W   = 14;

  parameter int unsigned REGCAP_W  = 38;

  parameter int unsigned RESETEXP  = 24;
  parameter int unsigned UPPER_W   = 24;
  parameter int unsigned RESETCEXP = 15;

  // bit index of PERMS field
  // U1 U0 SE US EX SR MC LD SL LM SD LG GL
  parameter int unsigned PERM_GL =  0;     // global flag
  parameter int unsigned PERM_LG =  1;     // load global
  parameter int unsigned PERM_SD =  2;     // store
  parameter int unsigned PERM_LM =  3;     // load mutable
  parameter int unsigned PERM_SL =  4;     // store local
  parameter int unsigned PERM_LD =  5;     // load
  parameter int unsigned PERM_MC =  6;     // capability load/store
  parameter int unsigned PERM_SR =  7;     // access system registes
  parameter int unsigned PERM_EX =  8;     // execution
  parameter int unsigned PERM_US =  9;     // unseal
  parameter int unsigned PERM_SE = 10;     // seal
  parameter int unsigned PERM_U0 = 11;     //
  parameter int unsigned PERM_U1 = 12;     //
  parameter int unsigned PERM_U2 = 13;     // temp workaround

  parameter logic [2:0] OTYPE_SENTRY_IE  = 3'd3;
  parameter logic [2:0] OTYPE_SENTRY_ID  = 3'd2;
  parameter logic [2:0] OTYPE_SENTRY     = 3'd1;
  parameter logic [2:0] OTYPE_UNSEALED   = 3'd0;

  // Compressed (regFile) capability type
  typedef struct packed {
    logic                valid;
    logic [1:0]          top_cor;
    logic [1:0]          base_cor;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [TOP_W-1   :0] top;
    logic [BOT_W-1   :0] base;
    logic [OTYPE_W-1 :0] otype;
    logic [CPERMS_W-1:0] cperms;
  } reg_cap_t;

  typedef struct packed {
    logic                valid;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [OTYPE_W-1 :0] otype;
    logic [PERMS_W-1: 0] perms;
    logic [1:0]          top_cor;
    logic [1:0]          base_cor;
    logic [TOP_W-1   :0] top;
    logic [BOT_W-1   :0] base;
    logic [CPERMS_W-1:0] cperms;
    logic [31:0]         maska;
    logic [31:0]         rlen;
  } full_cap_t;

  typedef struct packed {
    logic                valid;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [OTYPE_W-1 :0] otype;
    logic [PERMS_W-1: 0] perms;
    logic [TOP_W-1   :0] top;
    logic [BOT_W-1   :0] base;
    logic [CPERMS_W-1:0] cperms;
  } pcc_cap_t;

  typedef struct packed {
    logic [32:0]      top33req;
    logic [EXP_W-1:0] exp1;
    logic [EXP_W-1:0] exp2;
  } bound_req_t;

  parameter reg_cap_t  NULL_REG_CAP  = '{0, 0, 0, 0, 0, 0, 0, 0};
  parameter full_cap_t NULL_FULL_CAP = '{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  parameter pcc_cap_t  NULL_PCC_CAP  = '{0, 0, 0, 0, 0, 0, 0, 0, 0};

`ifndef USE_OLD_PERMS
  parameter logic [6:0] CPERMS_TX = 7'b0101111;  // Tx (execution root)
  parameter logic [6:0] CPERMS_TM = 7'b0111111;  // Tm (memory data root)
  parameter logic [6:0] CPERMS_TS = 7'b0100111;  // Tx (seal root)
`else
  parameter logic [6:0] CPERMS_TX = 7'h57;  // Tx (execution root)
  parameter logic [6:0] CPERMS_TM = 7'h7f;  // Tm (memory data root)
  parameter logic [6:0] CPERMS_TS = 7'h4f;  // Tx (seal root)
`endif

  parameter pcc_cap_t PCC_RESET_CAP   = '{1'b1, RESETEXP, 33'h10000_0000, 0, OTYPE_UNSEALED, 13'h1eb, 9'h100, 0, CPERMS_TX};   // Tx (execution root)

  parameter reg_cap_t  MTVEC_RESET_CAP     = '{1'b1, 1'b0, 1'b0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TX};   // Tx (execution root)
  parameter reg_cap_t  MTDC_RESET_CAP      = '{1'b1, 1'b0, 1'b0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TM};   // Tm
  parameter reg_cap_t MEPC_RESET_CAP       = '{1'b1, 1'b0, 1'b0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TX};   // Tx
  parameter reg_cap_t  MSCRATCHC_RESET_CAP = '{1'b1, 1'b0, 1'b0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TS};   // Ts


  parameter logic [PERMS_W-1: 0] PERM_MC_IMSK = (1<<PERM_LD) | (1<<PERM_MC) | (1<<PERM_SD);
  parameter logic [PERMS_W-1: 0] PERM_LC_IMSK = (1<<PERM_LD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_SC_IMSK = (1<<PERM_SD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_DD_IMSK = 0;
  parameter logic [PERMS_W-1: 0] PERM_EX_IMSK = (1<<PERM_EX) | (1<<PERM_MC) | (1<<PERM_LD);
  parameter logic [PERMS_W-1: 0] PERM_SE_IMSK = 0;

 `ifndef USE_OLD_PERMS
  // expand the perms from memory representation
  function automatic logic [PERMS_W-1:0] expand_perms(logic [CPERMS_W-1:0] cperms);
    logic [PERMS_W-1:0] perms;

    perms = 0;
    perms[PERM_GL] = cperms[5];

    if (cperms[4:3] == 2'b11) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms[PERM_SL] = cperms[2];
      perms          = perms | PERM_MC_IMSK;
    end else if (cperms[4:2] == 3'b101) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms          = perms | PERM_LC_IMSK;
    end else if (cperms[4:0] == 5'b10000) begin
      perms = perms | PERM_SC_IMSK;
    end else if (cperms[4:2] == 3'b100) begin
      perms[PERM_SD] = cperms[0];
      perms[PERM_LD] = cperms[1];
      perms          = perms | PERM_DD_IMSK;
    end else if (cperms[4:3] == 2'b01) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms[PERM_SR] = cperms[2];
      perms          = perms | PERM_EX_IMSK;
    end else if (cperms[4:3] == 2'b00) begin
      perms[PERM_US] = cperms[0];
      perms[PERM_SE] = cperms[1];
      perms[PERM_U0] = cperms[2];
      perms          = perms | PERM_SE_IMSK;
    end

    return perms;
  endfunction

  // test the implict permission mask (any bits not 1?)
  `define TEST_IMSK(P, M) (&((P) | ~(M)))

  // compress perms field to memory representation
  function automatic logic [CPERMS_W-1:0] compress_perms (logic [PERMS_W-1:0] perms, logic [1:0] qqq);   // qqq is a place holder, just to compatible with the old encoding for now.
    logic [CPERMS_W-1:0] cperms;

    // test all types encoding and determine encoding (Robert's priority order)
    // Encoding explicit bits based on type
    cperms    = 0;
    cperms[5] = perms[PERM_GL];

    if (`TEST_IMSK(perms, PERM_EX_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[2]   = perms[PERM_SR];
      cperms[4:3] = 2'b01;
    end else if (`TEST_IMSK(perms, PERM_MC_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[2]   = perms[PERM_SL];
      cperms[4:3] = 2'b11;
    end else if (`TEST_IMSK(perms, PERM_LC_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[4:2] = 3'b101;
    end else if (`TEST_IMSK(perms, PERM_SC_IMSK)) begin
      cperms[4:0] = 5'b10000;
    end else if (perms[PERM_SD] | perms[PERM_LD]) begin
      cperms[0]   = perms[PERM_SD];
      cperms[1]   = perms[PERM_LD];
      cperms[4:2] = 3'b100;
    end else begin
      cperms[0]   = perms[PERM_US];
      cperms[1]   = perms[PERM_SE];
      cperms[2]   = perms[PERM_U0];
      cperms[4:3] = 2'b00;
    end

    //$display("-------compress_perms:%t: %x - %x", $time, perms, cperms);
    return cperms;
  endfunction

  // handling cperms in loaded cap based on the loading cap requirment
  function automatic logic [CPERMS_W-1:0] mask_clcperms (logic [CPERMS_W-1:0] cperms_in, logic [3:0] clrperm,
                                                   logic valid_in, logic sealed);
    logic [CPERMS_W-1:0] cperms_out;
    logic                clr_glg, clr_sdlm;

    clr_glg   = clrperm[0] & valid_in;
    clr_sdlm  = clrperm[1] & valid_in & ~sealed;  // only clear SD/LM if not sealed

    cperms_out    = cperms_in;
    cperms_out[5] = cperms_in[5] & ~clr_glg;         // GL

    if (cperms_in[4:3] == 2'b11) begin
      cperms_out[0] = cperms_in[0] & ~clr_glg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
      cperms_out[4:2] = clr_sdlm ? 3'b101 : cperms_in[4:2];
    end else if (cperms_in[4:2] == 3'b101) begin
      cperms_out[0] = cperms_in[0] & ~clr_glg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end else if (cperms_in[4:0] == 5'b10000) begin
      cperms_out[4:0] = clr_sdlm? 5'h0 : cperms_in[4:0];   // clear SD will results in NULL permission
    end else if (cperms_in[4:2] == 3'b100) begin
      cperms_out[0] = cperms_in[0] & ~clr_sdlm;
    end else if (cperms_in[4:3] == 2'b01) begin
      cperms_out[0] = cperms_in[0] & ~clr_glg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end

    return cperms_out;
  endfunction

`else
  // expand the perms from memory representation
  function automatic logic [PERMS_W-1:0] expand_perms(logic [CPERMS_W-1:0] cperms);
    logic [PERMS_W-1:0] perms;

    perms = 0;

    if (cperms[5]) begin                      // "memory" type capability
      perms[PERM_LD] = 1'b1;
      perms[PERM_GL] = cperms[6];
      perms[PERM_MC] = cperms[4];
      perms[PERM_SL] = cperms[3];
      perms[PERM_LM] = cperms[2];
      perms[PERM_SD] = cperms[1];
      perms[PERM_LG] = cperms[0];
    end else if (cperms[5:4] == 2'b01) begin  // "execute" type capability
      perms[PERM_EX] = 1'b1;
      perms[PERM_LD] = 1'b1;
      perms[PERM_MC] = 1'b1;
      perms[PERM_GL] = cperms[6];
      perms[PERM_LM] = cperms[2];
      perms[PERM_SR] = cperms[1];
      perms[PERM_LG] = cperms[0];
      perms[PERM_U2] = cperms[3];
    end else if (cperms[5:4] == 2'b00) begin  // "execute" type capability
      perms[PERM_GL] = cperms[6];
      perms[PERM_U1] = cperms[3];
      perms[PERM_U0] = cperms[2];
      perms[PERM_SE] = cperms[1];
      perms[PERM_US] = cperms[0];
    end

    return perms;
  endfunction

  // compress perms field to memory representation
  function automatic logic [CPERMS_W-1:0] compress_perms(logic [PERMS_W-1:0] perms, logic [1:0] perm_type);
    logic [CPERMS_W-1:0] cperms;

    if (perm_type[1]) begin                    // "memory" type capabilities
      cperms[6] = perms[PERM_GL];              // GL 1 MC SL LM SD LG
      cperms[5] = 1'b1;
      cperms[4] = perms[PERM_MC];
      cperms[3] = perms[PERM_SL];
      cperms[2] = perms[PERM_LM];
      cperms[1] = perms[PERM_SD];
      cperms[0] = perms[PERM_LG];
    end else if (perm_type == 2'b01) begin     // "execute" tyep capabilities
      cperms[6] = perms[PERM_GL];              // GL 0 1 0 LM SR LG
      cperms[5] = 1'b0;
      cperms[4] = 1'b1;
      // cperms[3] = 1'b0;
      cperms[3] = perms[PERM_U2];
      cperms[2] = perms[PERM_LM];
      cperms[1] = perms[PERM_SR];
      cperms[0] = perms[PERM_LG];
    end else begin                             // "sealing" tyep capabilities
      cperms[6] = perms[PERM_GL];              // GL 0 0 U1 U0 SE US
      cperms[5] = 1'b0;
      cperms[4] = 1'b0;
      cperms[3] = perms[PERM_U1];
      cperms[2] = perms[PERM_U0];
      cperms[1] = perms[PERM_SE];
      cperms[0] = perms[PERM_US];
    end

    return cperms;
  endfunction

  // handling cperms in loaded cap based on the loading cap requirment
  function automatic logic [CPERMS_W-1:0] mask_clcperms (logic [CPERMS_W-1:0] cperms_in, logic [3:0] clrperm,
                                               logic valid_in, logic sealed);
    logic [CPERMS_W-1:0] cperms_out;
    logic [PERMS_W-1:0]  perms_tmp, perms_mask;
    logic                clr_glg, clr_sdlm;

    clr_glg   = clrperm[0];
    clr_sdlm  = clrperm[1];

    if (valid_in) begin    // only clear those fields for tagged(valid) caps
      perms_mask          = {PERMS_W{1'b1}};
      perms_mask[PERM_GL] = ~clr_glg;
      perms_mask[PERM_LG] = ~clr_glg;
      perms_mask[PERM_SD] = ~clr_sdlm | sealed;
      perms_mask[PERM_LM] = ~clr_sdlm | sealed;
      perms_tmp  = expand_perms(cperms_in) & perms_mask;
      cperms_out = compress_perms(perms_tmp, cperms_in[5:4]);
  //$display("%x %x %x", cperms_in, cperms_out, perms_mask);
    end else begin
      cperms_out = cperms_in;
    end

    return cperms_out;
  endfunction
`endif

  // caculate length (mem size) in bytes of a capability
  function automatic logic[31:0] get_cap_len (full_cap_t full_cap);
    logic [32:0] tmp33;
    logic [31:0] result;

    tmp33  = full_cap.top33 - full_cap.base32;
    result = tmp33[32]? 32'hffff_ffff: tmp33[31:0];

    return result;
  endfunction

  // obtain 32-bit representation of top/base
  function automatic logic[32:0] get_bound33(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                             logic [EXP_W-1:0] exp, logic [31:0] addr);
    logic [32:0] t1, t2, mask, cor_val;

    if (cor[1])
      cor_val = {33{cor[1]}};         // negative sign extension
    else
      cor_val = (~cor[1]) & cor[0];

    cor_val = (cor_val << exp) << TOP_W;
    mask    = (33'h1_ffff_ffff << exp) << TOP_W;

    t1 = (addr & mask) + cor_val;     // apply correction and truncate
//$display("gb33: corval=%09x, mask=%09x, t1=%09x", cor_val, mask, t1);
    t2 = top;                         // extend to 32 bit
    t1 = t1 | (t2 << exp);

    return t1;

  endfunction

  // this implementation give slightly better timing/area results
  function automatic logic[32:0] get_bound33_trial(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                             logic [EXP_W-1:0] exp, logic [31:0] addr);
    logic [32:0] t33a, t33b, result;
    logic [23:0] t24a, t24b, mask24, cor24;

    if (cor[1])
      cor24 = {24{cor[1]}};         // negative sign extension
    else
      cor24 = (~cor[1]) & cor[0];

    cor24  = (cor24 << exp);
    mask24 = {24{1'b1}} << exp;

    t24a = (addr[31:9] & mask24) + cor24;     // apply correction and truncate
//$display("gb33: corval=%09x, mask=%09x, t1=%09x", cor_val, mask, t1);
    t33a = top;
    result = {t24a, 9'h0} | (t33a << exp);

    return result;

  endfunction

  // update the top/base correction for a cap
  function automatic logic [3:0] update_temp_fields(logic [TOP_W-1:0] top, logic [BOT_W-1:0] base,
                                                    logic [BOT_W-1:0] addrmi);
    logic top_hi, addr_hi;
    logic [3:0] res4;

    top_hi   = (top < base);
    addr_hi  = (addrmi < base);

    // top_cor
    res4[3:2] = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);

    // base_cor
    res4[1:0] = (addr_hi) ? 2'b11 : 0;

    return res4;
  endfunction

  // set address of a capability
  //   by default we check for representability only. 
  //   use checktop/checkbase to check explicitly against top33/base32 bounds (pcc updates)
  //   * note, representability check in most cases (other than exp=24) covers the base32 check 

  function automatic full_cap_t set_address (full_cap_t in_cap, logic [31:0] newptr, logic chktop, logic chkbase);
    full_cap_t        out_cap;
    logic [32:0]      tmp33;
    logic [32-TOP_W:0] tmp24, mask24;
    logic  [3:0]      tmp4;
    logic [BOT_W-1:0] ptrmi9;
    logic             top_lt;

    out_cap = in_cap;
    mask24  = {(33-TOP_W){1'b1}} << in_cap.exp;          // mask24 = 0 if exp == 24

    tmp33   = {1'b0, newptr} - {1'b0, in_cap.base32};  // extend to make sure we can see carry from MSB
    tmp24   = tmp33[32:TOP_W] & mask24;
    top_lt  =  (newptr < {in_cap.top33[32:1], 1'b0});

    if ((tmp24 != 0) || (chktop & ~top_lt) || (chkbase & tmp33[32]))
      out_cap.valid = 1'b0;

    ptrmi9           = newptr >> in_cap.exp;
    tmp4             = update_temp_fields(out_cap.top, out_cap.base, ptrmi9);
    out_cap.top_cor  = tmp4[3:2];
    out_cap.base_cor = tmp4[1:0];

    return out_cap;
  endfunction

  // utillity function
  // return the size (bit length) of input number without leading zeros
  function automatic logic [5:0] get_size(logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32, b32;
    int i;

    a32 = {din[31], 31'h0};
    for (i = 30; i >=  0; i--) a32[i] = a32[i+1] | din[i];

    if (a32[31]) count = 32;
    else begin
      count[5] = 1'b0;
      count[4] = a32[15];
      b32 = count[4] ? a32[31:16] : a32[15:0];
      count[3] = b32[7];
      b32 = count[3] ?  b32[15:8]: b32[7:0];
      count[2] = b32[3];
      b32 = count[2] ?  b32[7:4] : b32[3:0];
      count[1] = b32[1];
      b32 = count[1] ? b32[3:2] : b32[1:0];
      count[0] = b32[0];
    end

    return count;
  endfunction

  // set bounds (top/base/exp/addr) of a capability

  // break up into 2 parts to enable 2-cycle option
  function automatic bound_req_t prep_bound_req (logic [31:0] addr, logic [31:0] length);
    bound_req_t result;
    result.top33req = {1'b0, addr} + {1'b0, length};    // "requested" 33-bit top

    result.exp1     = get_size({23'h0, length[31:9]});
    result.exp1     = (result.exp1 >= RESETCEXP) ? RESETEXP : result.exp1;
    result.exp2     = result.exp1+1;
    result.exp2     = (result.exp2 >= RESETCEXP) ? RESETEXP : result.exp2;

    return result;
  endfunction

  function automatic full_cap_t set_bounds (full_cap_t in_cap, logic[31:0] addr,
                                            bound_req_t bound_req, logic req_exact);
    full_cap_t       out_cap;

    logic [EXP_W-1:0] exp1, exp2, expr;
    logic [32:0]      top33req;
    logic [9:0]       base1, base2, top1, top2, len1, len2;
    logic [32:0]      mask1, mask2;
    logic             ovrflw, topoff1, topoff2, topoff;
    logic             baseoff1, baseoff2, baseoff;
    logic             tophi1, tophi2, tophi;

    out_cap  = in_cap;

    top33req = bound_req.top33req;
    exp1     = bound_req.exp1;
    exp2     = bound_req.exp2;

    // 1st path
    mask1    = {33{1'b1}} << exp1;
    base1    = addr >> exp1;
    topoff1  = |(top33req & ~mask1);
    baseoff1 = |(addr & ~mask1);
    top1     = (top33req >> exp1) + topoff1;
    len1     = top1 - base1;
    tophi1   = (top1[8:0] >= base1[8:0]);

    // overflow detection based on 1st path
    ovrflw = len1[9];

    // 2nd path in parallel
    mask2    = {33{1'b1}} << exp2;
    base2    = addr >> exp2;
    topoff2  = |(top33req & ~mask2);
    baseoff2 = |(addr & ~mask2);
    top2     = (top33req >> exp2) + topoff2;
    len2     = top2 - base2;
    tophi2   = (top2[8:0] >= base2[8:0]);

    // select results
    if (~ovrflw) begin
      out_cap.exp   = exp1;
      out_cap.top   = top1;
      out_cap.base  = base1;
      out_cap.maska = mask1;
      out_cap.rlen  = len1 << exp1;
      topoff        = topoff1;
      baseoff       = baseoff1;
      tophi         = tophi1;
    end else begin
      out_cap.exp   = exp2;
      out_cap.top   = top2;
      out_cap.base  = base2;
      out_cap.maska = mask2;
      out_cap.rlen  = len2 << exp2;
      topoff        = topoff2;
      baseoff       = baseoff2;
      tophi         = tophi2;
    end

`ifdef CHERI_PKG_DEBUG

$display("--- set_bounds: exact = %x, ovrflw = %x, exp1 = %x, exp2 = %x, exp = %x, len = %x", ~(topoff|baseoff), ovrflw, exp1, exp2, out_cap.exp, out_cap.rlen);
$display("--- set_bounds:  b1 = %x, t1 = %x, b2 = %x, t2 = %x", base1, top1, base2, top2);
`endif

    // Note in this case always addr >= base, but top < base or address is possible
    //   so - addr_hi = FALSE, top_cor can only be either either 0 or +1;
    out_cap.top_cor  = tophi ? 2'b00 : 2'b01;
    out_cap.base_cor = 2'b00;

    if (req_exact & (topoff | baseoff)) out_cap.valid = 1'b0;

    // we used the "requested top" to verify the results against original bounds
    if (top33req > in_cap.top33 ) out_cap.valid = 1'b0;

    return out_cap;
  endfunction

  // seal/unseal related functions
  function automatic full_cap_t seal_cap (full_cap_t in_cap, logic [OTYPE_W-1:0] new_otype);
    full_cap_t out_cap;

    out_cap = in_cap;
    out_cap.otype = new_otype;
    return out_cap;
  endfunction

  function automatic full_cap_t unseal_cap (full_cap_t in_cap);
    full_cap_t out_cap;
    out_cap = in_cap;
    out_cap.otype = OTYPE_UNSEALED;
    return out_cap;
  endfunction

  function automatic logic is_cap_sealed (full_cap_t in_cap);
    logic result;

    result = (in_cap.otype != OTYPE_UNSEALED);
    return result;
  endfunction

  function automatic logic is_cap_sentry (full_cap_t in_cap);
    logic result;

    result = (in_cap.otype == OTYPE_SENTRY) || (in_cap.otype == OTYPE_SENTRY_ID) ||
             (in_cap.otype == OTYPE_SENTRY_IE);
    return result;
  endfunction


  function automatic logic [3:0] decode_otype (logic [2:0] otype3, logic perm_ex);
    logic [3:0] otype4;

    otype4 = {~perm_ex & (otype3 != 0), otype3};
    return otype4;
  endfunction

  // reg_cap decompression (to full_cap)
  function automatic full_cap_t reg2fullcap (reg_cap_t reg_cap, logic [31:0] addr);
    full_cap_t full_cap;

    full_cap.perms    = expand_perms(reg_cap.cperms);
    full_cap.valid    = reg_cap.valid;
    full_cap.exp      = reg_cap.exp;
    full_cap.otype    = reg_cap.otype;
    full_cap.top_cor  = reg_cap.top_cor;
    full_cap.base_cor = reg_cap.base_cor;
    full_cap.top      = reg_cap.top;
    full_cap.base     = reg_cap.base;
    full_cap.cperms   = reg_cap.cperms;

    full_cap.top33  = get_bound33(reg_cap.top, reg_cap.top_cor, reg_cap.exp, addr);
    full_cap.base32 = get_bound33(reg_cap.base, reg_cap.base_cor, reg_cap.exp, addr);
    // full_cap  = update_bounds(full_cap, addr);   // for some reason this increases area 

    full_cap.maska    = 0;
    full_cap.rlen     = 0;

    return full_cap;
  endfunction

  // full_cap compression (to reg_cap).
  //   note we don't recalculate top/base_cor here since the address/bounds of a capability
  //   won't change without an explicit instruction (only exception is PCC)
  function automatic reg_cap_t full2regcap (full_cap_t full_cap);
    reg_cap_t reg_cap;

    reg_cap          = NULL_REG_CAP;
    reg_cap.valid    = full_cap.valid;
    reg_cap.top_cor  = full_cap.top_cor;
    reg_cap.base_cor = full_cap.base_cor;
    reg_cap.exp      = full_cap.exp;
    reg_cap.top      = full_cap.top;
    reg_cap.base     = full_cap.base;
    reg_cap.cperms   = full_cap.cperms;
    reg_cap.otype    = full_cap.otype;

    return reg_cap;
  endfunction

  // pcc_cap expansion (to full_cap).
  //  -- pcc is a special case since the address (PC) moves around..
  //     so have to adjust correction factors and validate bounds here
  function automatic full_cap_t pcc2fullcap (pcc_cap_t pcc_cap, logic [31:0] pc_addr);
    logic [3:0] tmp4;
    full_cap_t full_cap;
    logic [BOT_W-1:0] pcmi9;

    pcmi9             = pc_addr >> pcc_cap.exp;
    tmp4              = update_temp_fields(pcc_cap.top, pcc_cap.base, pcmi9);
    full_cap          = NULL_REG_CAP;
    full_cap.valid    = pcc_cap.valid;
    full_cap.perms    = pcc_cap.perms;
    full_cap.top_cor  = tmp4[3:2];
    full_cap.base_cor = tmp4[1:0];
    full_cap.exp      = pcc_cap.exp;
    full_cap.top      = pcc_cap.top;
    full_cap.base     = pcc_cap.base;
    full_cap.cperms   = pcc_cap.cperms;
    full_cap.otype    = pcc_cap.otype;
    full_cap.top33    = pcc_cap.top33;
    full_cap.base32   = pcc_cap.base32;
    full_cap.maska    = 0;
    full_cap.rlen     = 0;

    return full_cap;
  endfunction

  // compress full_cap to pcc_cap
  function automatic pcc_cap_t full2pcap (full_cap_t full_cap);
    pcc_cap_t pcc_cap;

    pcc_cap.perms    = full_cap.perms;
    pcc_cap.valid    = full_cap.valid;
    pcc_cap.exp      = full_cap.exp;
    pcc_cap.otype    = full_cap.otype;
    pcc_cap.top      = full_cap.top;
    pcc_cap.base     = full_cap.base;
    pcc_cap.cperms   = full_cap.cperms;
    pcc_cap.top33    = full_cap.top33;
    pcc_cap.base32   = full_cap.base32;

    return pcc_cap;
  endfunction


  //
  // pack/unpack the cap+addr between reg and memory
  // format 0: lsw32 = addr, msw33 = cap fields
  //
  // p’7 otype’3 E’4 B’9 T’9
  localparam integer CPERMS_LO = 25;
  localparam integer OTYPE_LO  = 22;
  localparam integer CEXP_LO   = 18;
  localparam integer BASE_LO   = 9;
  localparam integer TOP_LO    = 0;

  function automatic reg_cap_t mem2regcap_fmt0 (logic [32:0] msw, logic [32:0] addr33, logic [3:0] clrperm);
    reg_cap_t regcap;
    logic [31:0] tmp32;
    logic  [3:0] tmp4;
    logic [CPERMS_W-1:0] cperms_mem;
    logic [BOT_W-1:0]    addrmi9;
    logic                sealed;

    regcap.valid  = msw[32] & addr33[32] & ~clrperm[3];   // AND the valid bits for now

    tmp32    = msw[CEXP_LO+:CEXP_W];
    if (tmp32 == RESETCEXP) tmp32 = RESETEXP;
    regcap.exp    = tmp32;

    regcap.top    = msw[TOP_LO+:TOP_W];
    regcap.base   = msw[BASE_LO+:BOT_W];
    regcap.otype  = msw[OTYPE_LO+:OTYPE_W];

    sealed = (regcap.otype != OTYPE_UNSEALED);
    cperms_mem    = msw[CPERMS_LO+:CPERMS_W];
    regcap.cperms = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);
    addrmi9         = addr33 >> regcap.exp;
    tmp4            = update_temp_fields(regcap.top, regcap.base, addrmi9);
    regcap.top_cor  = tmp4[3:2];
    regcap.base_cor = tmp4[1:0];
    return regcap;

  endfunction

  function automatic logic[32:0] reg2memcap_fmt0 (reg_cap_t regcap);

    logic [32:0] msw;

    msw[32] = regcap.valid ;

    msw[CEXP_LO+:CEXP_W]     = (regcap.exp == RESETEXP) ? RESETCEXP : regcap.exp[CEXP_W-1:0];
    msw[TOP_LO+:TOP_W]       = regcap.top   ;
    msw[BASE_LO+:BOT_W]      = regcap.base  ;
    msw[OTYPE_LO+:OTYPE_W]   = regcap.otype ;
    msw[CPERMS_LO+:CPERMS_W] = regcap.cperms;

    return msw;

  endfunction

  //
  // pack/unpack the cap+addr between reg and memory
  // format 1: lsw32 = GL+ EXP+B+T+A addr, msw33 = rest of the fields
  //

  function automatic reg_cap_t mem2regcap_fmt1 (logic [32:0] msw, logic [32:0] lsw, logic [3:0] clrperm);
    reg_cap_t regcap;
    logic [31:0] tmp32;
    logic        sealed;
    logic [8:0]  addrmi9;
    logic [CPERMS_W-1:0] cperms_mem;

    // lsw is now EXP+B+T+A
    regcap.valid  = msw[32] & lsw[32] & ~clrperm[3];   // AND the valid bits for now
    regcap.exp    = (lsw[30:27] == RESETCEXP) ?  RESETEXP : {1'b0, lsw[30:27]};
    regcap.base   = lsw[26:18];
    regcap.top    = lsw[17:9];
    addrmi9       = (lsw[30:27] == RESETCEXP) ? lsw[8:1] : lsw[8:0];

    regcap.otype  = msw[25:23];
    sealed        = (regcap.otype != OTYPE_UNSEALED);

    cperms_mem = {lsw[31], msw[31:26]};
    regcap.cperms = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);

    tmp32 = update_temp_fields(regcap.top, regcap.base, addrmi9);
    regcap.top_cor  = tmp32[3:2];
    regcap.base_cor = tmp32[1:0];

    return regcap;

  endfunction

  function automatic logic[32:0] mem2regaddr_fmt1 (logic [32:0] msw, logic [32:0] lsw, reg_cap_t reg_cap);
    logic [32:0] addr33;
    logic [31:0] addrmi, addrhi, addrlo;
    logic [31:0] mask1, mask2;

    if (reg_cap.exp == RESETEXP) begin
      addrhi   = 33'h0;
      addrmi   = {lsw[8:0], 23'h0};
      addrlo   = msw[22:0];
    end else begin
      addrmi   = lsw[8:0] << reg_cap.exp;
      mask1    = {33{1'b1}} << reg_cap.exp;
      mask2    = mask1 << 9;
      addrhi   = (msw[22:0] << 9) & mask2;
      addrlo   = msw[22:0] & (~mask1);
    end

    addr33 = {lsw[32], addrhi | addrmi |addrlo};

    return addr33;
  endfunction

  function automatic logic[65:0] reg2mem_fmt1 (reg_cap_t reg_cap, logic[31:0] addr);

    logic [32:0] msw, lsw;
    logic [31:0] mask1, mask2;

    msw[32]    = reg_cap.valid;
    msw[31:26] = reg_cap.cperms[5:0];
    msw[25:23] = reg_cap.otype;
    lsw[32]    = reg_cap.valid ;
    lsw[31]    = reg_cap.cperms[6];
    lsw[26:18] = reg_cap.base;
    lsw[17:9]  = reg_cap.top;

    if (reg_cap.exp == RESETEXP) begin
      msw[22:0]  = addr[22:0];
      lsw[30:27] = RESETCEXP;
      lsw[8:0]   = addr[31:23];
    end else begin
      mask1    = {33{1'b1}} << reg_cap.exp;
      mask2    = mask1 << 9;

      msw[22:0]  = (addr & ~mask1) | ((addr & mask2) >> 9);
      lsw[30:27] = reg_cap.exp[CEXP_W-1:0];
      lsw[8:0]   = addr >> reg_cap.exp;
    end

    return {msw, lsw};

  endfunction

  // simply cast regcap to a 38-bit vector. 
  // we can do this with systemverilog casting but let's be explicit here
  function automatic logic [REGCAP_W-1:0] reg2vec (reg_cap_t regcap);

    logic [REGCAP_W-1:0] vec_out;

    vec_out[REGCAP_W-1]  = regcap.valid ;
    vec_out[35+:2]       = regcap.top_cor;
    vec_out[33+:2]       = regcap.base_cor;
    vec_out[28+:EXP_W]   = regcap.exp;
    vec_out[19+:TOP_W]   = regcap.top   ;
    vec_out[10+:BOT_W]   = regcap.base  ;
    vec_out[7+:OTYPE_W]  = regcap.otype ;
    vec_out[0+:CPERMS_W] = regcap.cperms;

    return vec_out;
  endfunction

  function automatic reg_cap_t vec2reg (logic [REGCAP_W-1:0] vec_in);

    reg_cap_t regcap;

    regcap.valid    = vec_in[REGCAP_W-1];  
    regcap.top_cor  = vec_in[35+:2];       
    regcap.base_cor = vec_in[33+:2];       
    regcap.exp      = vec_in[28+:EXP_W];   
    regcap.top      = vec_in[19+:TOP_W];   
    regcap.base     = vec_in[10+:BOT_W];   
    regcap.otype    = vec_in[7+:OTYPE_W];  
    regcap.cperms   = vec_in[0+:CPERMS_W]; 

    return regcap;
  endfunction

  // test whether 2 caps are equal
  function automatic logic is_equal (full_cap_t cap_a, full_cap_t cap_b);

    is_equal =  (cap_a.valid  == cap_b.valid) &&
                (cap_a.top33  == cap_b.top33) && (cap_a.base32 == cap_b.base32) &&
                (cap_a.perms  == cap_b.perms) &&
                (cap_a.exp    == cap_b.exp) && (cap_a.otype  == cap_b.otype);
    return is_equal;

  endfunction

  // parameters and constants

  parameter logic[6:0] CHERI_INSTR_OPCODE = 7'h5b;
  parameter int OPDW = 36;      // Must >= number of cheri operator/instructions we support

  typedef enum logic [5:0] {
    CGET_PERM       = 6'h00,
    CGET_TYPE       = 6'h01,
    CGET_BASE       = 6'h02,
    CGET_LEN        = 6'h03,
    CGET_TAG        = 6'h04,
    CGET_TOP        = 6'h05,
//    CGET_OFFSET     = 6'h06,
    CGET_ADDR       = 6'h07,
    CSEAL           = 6'h08,
    CUNSEAL         = 6'h09,
    CAND_PERM       = 6'h0a,
    CSET_ADDR       = 6'h0b,
    CINC_ADDR       = 6'h0c,
    CINC_ADDR_IMM   = 6'h0d,
    CSET_BOUNDS     = 6'h0e,
    CSET_BOUNDS_EX  = 6'h0f,
    CSET_BOUNDS_IMM = 6'h10,
    CIS_SUBSET      = 6'h11,
    CIS_EQUAL       = 6'h12,
    CMOVE_CAP       = 6'h13,
    CSUB_CAP        = 6'h14,
    CCLEAR_TAG      = 6'h15,
    CLOAD_CAP       = 6'h16,
    //CLBC            = 6'h17,
    CSTORE_CAP      = 6'h18,
    CCSR_RW         = 6'h19,
    CJALR           = 6'h1a,
    CJAL            = 6'h1b,
    CAUIPCC         = 6'h1c,
    CAUICGP         = 6'h1d,
    CRRL            = 6'h1e,
    CRAM            = 6'h1f
  } cheri_op_e;

  typedef enum logic [4:0] {
    CHERI_CSR_NULL,
    CHERI_CSR_RW
  } cheri_csr_op_e;

endpackage
