// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cheri_pkg;

  // bit field widths
  // IT8 encoding
  parameter int unsigned ADDR_W    = 32;
  parameter int unsigned TOP_W     = 9;    
  parameter int unsigned BOT_W     = 9;
  parameter int unsigned CEXP_W    = 5;
  parameter int unsigned EXP_W     = 5;
  parameter int unsigned OTYPE_W   = 3;
  parameter int unsigned CPERMS_W  = 6;
  parameter int unsigned PERMS_W   = 12;

  parameter bit    [4:0] RESETEXP  = 24;
  parameter bit    [4:0] RESETEXPINV = 7;
  parameter int unsigned UPPER_W   = 24;

  // bit index of PERMS field
  // U0 SE US EX SR MC LD SL LM SD LG GL
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

  parameter logic [2:0] OTYPE_SENTRY_IE_BKWD = 3'd5;
  parameter logic [2:0] OTYPE_SENTRY_ID_BKWD = 3'd4;
  parameter logic [2:0] OTYPE_SENTRY_IE_FWD  = 3'd3;
  parameter logic [2:0] OTYPE_SENTRY_ID_FWD  = 3'd2;
  parameter logic [2:0] OTYPE_SENTRY     = 3'd1;
  parameter logic [2:0] OTYPE_UNSEALED   = 3'd0;


  // Compressed (in-memory) capability type
  typedef struct packed {
    logic                valid;
    logic                rsvd;
    logic [CPERMS_W-1:0] cperms;
    logic [OTYPE_W-1 :0] otype;
    logic [EXP_W-1   :0] cexp;    // 
    logic [7         :0] top8;    // 8-bit
    logic [BOT_W-1   :0] base9;
    logic [31:0]         addr;
  } mem_cap_t;

  // reg_cap_t is not bit compatible with mem_cap_t
  typedef struct packed {
    logic                valid;
    logic                rsvd;
    logic [CPERMS_W-1:0] cperms;
    logic [OTYPE_W-1 :0] otype;
    logic [EXP_W-1   :0] exp;     // 
    logic [TOP_W-1   :0] top9;    // 9-bit
    logic [BOT_W-1   :0] base9;
    logic [31:0]         addr;
  } reg_cap_t;

  typedef struct packed {
    logic [1:0]          top_cor;
    logic                base_cor;
    // reg_cap fields
    logic                valid;
    logic                rsvd;
    logic [CPERMS_W-1:0] cperms;
    logic [OTYPE_W-1 :0] otype;
    logic [EXP_W-1   :0] exp;     // 
    logic [TOP_W-1   :0] top9;    // 9-bit
    logic [BOT_W-1   :0] base9;
    logic [31:0]         addr;
  } op_cap_t;

  typedef struct packed {
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [PERMS_W-1: 0] perms;
    // op_cap fields
    logic [1:0]          top_cor;
    logic                base_cor;
    // reg_cap fields
    logic                valid;
    logic                rsvd;
    logic [CPERMS_W-1:0] cperms;
    logic [OTYPE_W-1 :0] otype;
    logic [EXP_W-1   :0] exp;     // 
    logic [TOP_W-1   :0] top9;    // 9-bit
    logic [BOT_W-1   :0] base9;
    logic [31:0]         addr;
  } full_cap_t;

  // pcc_cap is the special case (pc not stored here)
  typedef struct packed {
    logic                valid;
    logic                rsvd;
    logic [CPERMS_W-1:0] cperms;
    logic [OTYPE_W-1 :0] otype;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [PERMS_W-1: 0] perms;
  } pcc_cap_t;

  typedef struct packed {
    logic [32:0]      top33req;
    logic [EXP_W-1:0] exp1;
    logic [EXP_W-1:0] exp2;
    logic [EXP_W:0]   explen;
    logic [EXP_W:0]   expb;   // this can be 32 so must be 6-bit
  } setbounds_req_t;

  typedef struct packed {
    logic [31:0] maska;
    logic [31:0] rlen;
    full_cap_t   fcap;
  } setbounds_out_t;

  localparam int unsigned MemCapW  = $bits(mem_cap_t);  // 65
  localparam int unsigned RegCapW  = $bits(reg_cap_t);
  localparam int unsigned OpCapW   = $bits(op_cap_t);
  localparam int unsigned FullCapW = $bits(full_cap_t);
  localparam int unsigned PccCapW  = $bits(pcc_cap_t);

  parameter int unsigned MEM_TAG = MemCapW-1;  // bit index for tag bit for mem cap formats
  parameter int unsigned REG_TAG = RegCapW-1;  // bit index for tag bit for internal (reg/op/full) cap formats 

  parameter reg_cap_t  NULL_REG_CAP  = reg_cap_t'(0);
  parameter op_cap_t   NULL_OP_CAP   = op_cap_t'(0);
  parameter full_cap_t NULL_FULL_CAP = full_cap_t'(0);
  parameter pcc_cap_t  NULL_PCC_CAP  = pcc_cap_t'(0);

  parameter setbounds_req_t NULL_SETBOUNDS_REQ = setbounds_req_t'(0);
  parameter setbounds_out_t NULL_SETBOUNDS_OUT = setbounds_out_t'(0);

  parameter logic [5:0] CPERMS_TX = 6'b101111;  // Tx (execution root)
  parameter logic [5:0] CPERMS_TM = 6'b111111;  // Tm (memory data root)
  parameter logic [5:0] CPERMS_TS = 6'b100111;  // Tx (seal root)

  // Tx (execution root)
  parameter pcc_cap_t PCC_RESET_CAP  = '{1'b1, 1'b0, CPERMS_TX, OTYPE_UNSEALED, RESETEXP, 33'h10000_0000, 0, 12'h1eb};

  parameter reg_cap_t TX_ROOT_RCAP   = '{1'b1, 1'b0, CPERMS_TX, OTYPE_UNSEALED, RESETEXP, 9'h100, 0, 0};   
  parameter reg_cap_t TM_ROOT_RCAP   = '{1'b1, 1'b0, CPERMS_TM, OTYPE_UNSEALED, RESETEXP, 9'h100, 0, 0};   
  parameter reg_cap_t TS_ROOT_RCAP   = '{1'b1, 1'b0, CPERMS_TS, OTYPE_UNSEALED, RESETEXP, 9'h100, 0, 0};   

  parameter logic [PERMS_W-1: 0] PERM_MC_IMSK = (1<<PERM_LD) | (1<<PERM_MC) | (1<<PERM_SD);
  parameter logic [PERMS_W-1: 0] PERM_LC_IMSK = (1<<PERM_LD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_SC_IMSK = (1<<PERM_SD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_DD_IMSK = 0;
  parameter logic [PERMS_W-1: 0] PERM_EX_IMSK = (1<<PERM_EX) | (1<<PERM_MC) | (1<<PERM_LD);
  parameter logic [PERMS_W-1: 0] PERM_SE_IMSK = 0;

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
  function automatic logic [CPERMS_W-1:0] compress_perms (logic [PERMS_W-1:0] perms, logic [1:0] unused_qqq);   // unused_qqq is a place holder, just to compatible with the old encoding for now.
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
    logic                clr_gl, clr_lg, clr_sdlm;

    clr_gl    = clrperm[0] & valid_in;
    clr_lg    = clrperm[0] & valid_in & ~sealed;
    clr_sdlm  = clrperm[1] & valid_in & ~sealed;  // only clear SD/LM if not sealed

    cperms_out    = cperms_in;
    cperms_out[5] = cperms_in[5] & ~clr_gl;         // GL

    if (cperms_in[4:3] == 2'b11) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
      cperms_out[4:2] = clr_sdlm ? 3'b101 : cperms_in[4:2];
    end else if (cperms_in[4:2] == 3'b101) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end else if (cperms_in[4:0] == 5'b10000) begin
      cperms_out[4:0] = clr_sdlm? 5'h0 : cperms_in[4:0];   // clear SD will results in NULL permission
    end else if (cperms_in[4:2] == 3'b100) begin
      cperms_out[4] = ~(clr_sdlm & ~cperms_in[1]);    // must decode to 5'h0 if both ld/sd are 0.
      cperms_out[0] = cperms_in[0] & ~clr_sdlm;
    end else if (cperms_in[4:3] == 2'b01) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end

    return cperms_out;
  endfunction

  // caculate length (mem size) in bytes of a capability
  function automatic logic[31:0] get_cap_len (full_cap_t full_cap);
    logic [32:0] tmp33;
    logic [31:0] result;

    tmp33  = full_cap.top33 - full_cap.base32;
    result = tmp33[32]? 32'hffff_ffff: tmp33[31:0];

    return result;
  endfunction

  // obtain 32-bit representation of top
  function automatic logic[32:0] get_bound33(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                             logic [EXP_W-1:0] exp, logic [31:0] addr);
    logic [32:0] t1, t2, mask, cor_val;

    if (cor[1])
      cor_val = {33{cor[1]}};         // negative sign extension
    else
      cor_val = {32'h0, (~cor[1]) & cor[0]};

    cor_val = (cor_val << exp) << TOP_W;
    mask    = (33'h1_ffff_ffff << exp) << TOP_W;

    t1 = ({1'b0, addr} & mask) + cor_val;     // apply correction and truncate
//$display("gb33: corval=%09x, mask=%09x, t1=%09x", cor_val, mask, t1);
    t2 = {24'h0, top};                         // extend to 32 bit
    t1 = t1 | (t2 << exp);

    return t1;

  endfunction

  // update the top/base correction for a cap
  function automatic logic [2:0] update_temp_fields(logic [TOP_W-1:0] top9, logic [BOT_W-1:0] base9,
                                                    logic [BOT_W-1:0] addrmi9);
    logic top_hi, addr_hi;
    logic [2:0] res3;

    top_hi   = (top9 < base9);
    addr_hi  = (addrmi9 < base9);

    // top_cor
    res3[2:1] = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);

    // base_cor
    res3[0] = addr_hi;

    return res3;
  endfunction

  // set address of a capability
  //   by default we check for representability only. 
  //   use checktop/checkbase to check explicitly against top33/base32 bounds (pcc updates)
  //   * note, representability check in most cases (other than exp=24) covers the base32 check 

  function automatic full_cap_t set_address (full_cap_t in_cap, logic [31:0] newptr);
    full_cap_t         out_cap;
    logic [32:0]       tmp33;
    logic [32-TOP_W:0] tmp24, mask24;
    logic [2:0]        tmp3;
    logic [BOT_W-1:0]  ptrmi9;
    logic              top_lt;
    logic [8:0]        top9, base9;

    out_cap      = in_cap;
    out_cap.addr = newptr;

    mask24  = {(33-TOP_W){1'b1}} << in_cap.exp;          // mask24 = 0 if exp == 24

    tmp33   = {1'b0, newptr} - {1'b0, in_cap.base32};  // extend to make sure we can see carry from MSB
    tmp24   = tmp33[32:TOP_W] & mask24;

    if (|tmp24) 
      out_cap.valid = 1'b0;

    top9    = out_cap.top9;
    base9   = out_cap.base9;     
    ptrmi9  = BOT_W'(newptr >> in_cap.exp);
    tmp3    = update_temp_fields(top9, base9, ptrmi9);

    out_cap.top_cor  = tmp3[2:1];
    out_cap.base_cor = tmp3[0];

    return out_cap;
  endfunction

  // pipelined version for timing
  function automatic full_cap_t set_address_lite (full_cap_t in_cap, logic [8:0] ptrmi9);
    full_cap_t         out_cap;
    logic [32:0]       tmp33;
    logic [32-TOP_W:0] tmp24, mask24;
    logic [2:0]        tmp3;
    logic              top_lt;
    logic [8:0]        top9, base9;
    logic [31:0]       newptr;

    out_cap = in_cap;
    newptr  = in_cap.addr;

    mask24  = {(33-TOP_W){1'b1}} << in_cap.exp;          // mask24 = 0 if exp == 24

    tmp33   = {1'b0, newptr} - {1'b0, in_cap.base32};  // extend to make sure we can see carry from MSB
    tmp24   = tmp33[32:TOP_W] & mask24;

    if (|tmp24) 
      out_cap.valid = 1'b0;

    top9    = out_cap.top9;
    base9   = out_cap.base9;     
    tmp3    = update_temp_fields(top9, base9, ptrmi9);

    out_cap.top_cor  = tmp3[2:1];
    out_cap.base_cor = tmp3[0];

   return out_cap;
  endfunction

  //
  // utility functions
  //

  // return the size (bit length) of input number without leading zeros
  function automatic logic [5:0] get_size(logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32;
    int i;

    a32 = {din[31], 31'h0};
    for (i = 30; i >=  0; i--) a32[i] = a32[i+1] | din[i];
    count = thermo_dec32(a32);

    return count;
  endfunction

  // return the exp of a 32-bit input (by count trailing zeros)
  function automatic logic [5:0] count_tz (logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32, b32;
    int i;

    a32 = {31'h0, din[0]};
    for (i = 1; i < 32; i++) a32[i] = a32[i-1] | din[i];
    // count = a32[31] ? thermo_dec32(~a32) : 0;       // if input all zero, return 0
    count = thermo_dec32(~a32);       // if input all zero, return 32

    return count;
  endfunction

  // this simply count the number of 1's in a thermoeter-encoded input vector
  //    (32-N zeros followed by N ones)
  // 
  function automatic logic [5:0] thermo_dec32(logic [31:0] a32);
    logic  [5:0] count;
    logic [31:0] b32;

    if (a32[31]) count = 32;
    else begin
      count[5] = 1'b0;
      count[4] = a32[15];
      b32[15:0] = count[4] ? a32[31:16] : a32[15:0];
      count[3] = b32[7];
      b32[ 7:0] = count[3] ? b32[15:8] : b32[7:0];
      count[2] = b32[3];
      b32[ 3:0] = count[2] ?  b32[7:4] : b32[3:0];
      count[1] = b32[1];
      b32[ 1:0] = count[1] ?  b32[3:2] : b32[1:0];
      count[0] = b32[0];
    end

    return count;
  endfunction

  // set bounds (top/base/exp/addr) of a capability

  // break up into 2 parts to enable 2-cycle option
  function automatic setbounds_req_t prep_bound_req(full_cap_t in_cap, logic [31:0] length);   
    setbounds_req_t result;
    logic [4:0]     size_result;
    logic           gt24;
    logic [4:0]     limit24_mask;

    result.top33req = {1'b0, in_cap.addr} + {1'b0, length};    // "requested" 33-bit top
    result.expb     = count_tz(in_cap.addr);
    result.explen   = get_size({9'h0, length[31:9]});   // length exp without saturation, max 23

    // since explen <= 23, exp1 and exp must be <= 24. No need for saturation logic
    result.exp1     = result.explen;   
    result.exp2     = result.explen + 1;

    return result;
  endfunction

  function automatic setbounds_out_t set_bounds (full_cap_t in_cap, setbounds_req_t bound_req, logic req_exact);
    setbounds_out_t   result;

    logic [EXP_W-1:0] exp1, exp2;
    logic [32:0]      top33req;
    logic [BOT_W:0]   base1, base2, top1, top2, len1, len2;
    logic [32:0]      mask1, mask2;
    logic             ovrflw, topoff1, topoff2, topoff;
    logic             baseoff1, baseoff2, baseoff;
    logic             tophi1, tophi2, tophi;
    logic             in_bound;

    result.fcap  = in_cap;

    top33req = bound_req.top33req;
    exp1     = bound_req.exp1;
    exp2     = bound_req.exp2;
    in_bound = ~((bound_req.top33req > in_cap.top33) || (in_cap.addr < in_cap.base32)); 


    // 1st path
    mask1    = {33{1'b1}} << exp1;
    base1    = (BOT_W+1)'(in_cap.addr >> exp1);
    topoff1  = |(top33req & ~mask1);
    baseoff1 = |({1'b0, in_cap.addr} & ~mask1);
    top1     = (BOT_W+1)'(top33req >> exp1) + (BOT_W+1)'(topoff1);
    len1     = top1 - base1;
    tophi1   = (top1[8:0] >= base1[8:0]);

    // overflow detection based on 1st path
    ovrflw = len1[9];

    // 2nd path in parallel
    mask2    = {33{1'b1}} << exp2;
    base2    = (BOT_W+1)'(in_cap.addr >> exp2);
    topoff2  = |(top33req & ~mask2);
    baseoff2 = |({1'b0, in_cap.addr} & ~mask2);
    top2     = (BOT_W+1)'(top33req >> exp2) + (BOT_W+1)'(topoff2);
    len2     = top2 - base2;
    tophi2   = (top2[8:0] >= base2[8:0]);

    // select results
    result.fcap.exp      = (~ovrflw) ? exp1 : exp2;
    //result.fcap.top8     = (~ovrflw) ? top1[7:0] : top2[7:0];
    result.fcap.top9     = (~ovrflw) ? top1[8:0] : top2[8:0];
    result.fcap.base9    = (~ovrflw) ? base1[BOT_W-1:0] : base2[BOT_W-1:0];
    result.maska         = (~ovrflw) ? mask1[31:0] : mask2[31:0];
    result.rlen          = (~ovrflw) ? ({22'h0, len1} << exp1) : ({22'h0, len2} << exp2);

    topoff      = (~ovrflw) ? topoff1: topoff2;
    baseoff     = (~ovrflw) ? baseoff1 : baseoff2;
    tophi       = (~ovrflw) ? tophi1: tophi2;

`ifdef CHERI_PKG_DEBUG

$display("--- set_bounds: exact = %x, ovrflw = %x, exp1 = %x, exp2 = %x, exp = %x, len = %x", ~(topoff|baseoff), ovrflw, exp1, exp2, result.fcap.exp, result.fcap.rlen);
$display("--- set_bounds:  b1 = %x, t1 = %x, b2 = %x, t2 = %x", base1, top1, base2, top2);
`endif

    // top/base correction values
    //   Note the new base == addr >> exp, so addr_hi == FALSE, thus base_cor == 0
    //   as such, top_cor can only be either either 0 or +1;
    result.fcap.top_cor  = tophi ? 2'b00 : 2'b01;
    result.fcap.base_cor = 1'b0;

    // we used the "requested top" to verify the results against original bounds
    // also compare address >= old base 32 to handle exp=24 case
    //   exp = 24 case: can have addr < base (not covered by representibility checking);
    //   other exp cases: always addr >= base when result.fcap.tag == 1

    if (~in_bound |(req_exact & (topoff | baseoff))) result.fcap.valid = 1'b0;

    return result;
  endfunction

  function automatic setbounds_out_t set_bounds_rndn (full_cap_t in_cap, setbounds_req_t bound_req);
    setbounds_out_t  result;

    logic [EXP_W:0]   explen, expb, exp_final;
    logic [32:0]      top33req;
    logic             in_bound;
    logic             el_gt_eb; 
    logic             tophi;
    logic [BOT_W-1:0] top9, base9;

    result.fcap = in_cap;
              
    top33req  = bound_req.top33req;
    explen    = bound_req.explen;
    expb      = bound_req.expb;
    in_bound  = ~((bound_req.top33req > in_cap.top33) || (in_cap.addr < in_cap.base32)); 
              
    el_gt_eb  = (explen > expb);
    
    exp_final = (el_gt_eb) ? expb :  explen;
    base9     = (BOT_W)'(in_cap.addr >> exp_final);
    top9      = (el_gt_eb) ? ((BOT_W)'(base9-1)) : ((BOT_W)'(top33req >> exp_final));

    result.fcap.exp     = exp_final;
    result.fcap.base9   = base9;
    result.fcap.top9    = top9;

    if (~in_bound) result.fcap.valid = 1'b0;

    // top/base correction values
    //   Note the new base == addr >> exp, so addr_hi == FALSE, thus base_cor == 0
    //   as such, top_cor can only be either either 0 or +1;
    tophi = (top9 >= base9);
    result.fcap.top_cor  = tophi ? 2'b00 : 2'b01;
    result.fcap.base_cor = 2'b00;
  
    result.maska         = 32'h0;
    result.rlen          = 32'h0;

    return result;
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

  // seal/unseal related functions
  function automatic logic is_cap_sealed (full_cap_t in_cap);
    logic result;

    result = (in_cap.otype != OTYPE_UNSEALED);
    return result;
  endfunction

  function automatic logic [3:0] decode_otype (logic [2:0] otype3, logic perm_ex);
    logic [3:0] otype4;

    otype4 = {~perm_ex & (otype3 != 0), otype3};
    return otype4;
  endfunction

  // op_cap decompression (to full_cap)
  function automatic full_cap_t op2fullcap (op_cap_t op_cap);
    full_cap_t full_cap;
    logic [8:0]      top9, base9;

    full_cap[OpCapW-1:0] = op_cap;

    // top9    = {op_cap.top_msb, op_cap.top8};
    top9    = op_cap.top9;
    base9   = op_cap.base9;     

    full_cap.perms  = expand_perms(op_cap.cperms);
    full_cap.top33  = get_bound33(top9, op_cap.top_cor, op_cap.exp, op_cap.addr);
    full_cap.base32 = get_bound33(base9, {2{op_cap.base_cor}}, op_cap.exp, op_cap.addr);

    return full_cap;
  endfunction

  // pcc_cap expansion (to full_cap).
  //  -- pcc is a special case since the address (PC) moves around..
  //     so have to adjust correction factors and validate bounds here
  // function automatic full_cap_t pcc2fullcap (pcc_cap_t pcc_cap, logic [31:0] pc_addr);
  function automatic full_cap_t pcc2fullcap (pcc_cap_t in_pcap, logic [31:0] addr);
    full_cap_t   pcc_fullcap;
    logic [8:0]  top9, base9;

    top9      = TOP_W'(in_pcap.top33  >> (in_pcap.exp));
    base9     = BOT_W'(in_pcap.base32 >> (in_pcap.exp));

    pcc_fullcap.valid    = in_pcap.valid;   
    pcc_fullcap.exp      = in_pcap.exp; 
    //pcc_fullcap.top8     = top9[7:0];
    pcc_fullcap.top9     = top9;
    pcc_fullcap.base9    = base9;
    pcc_fullcap.cperms   = in_pcap.cperms;
    pcc_fullcap.otype    = in_pcap.otype;
    pcc_fullcap.rsvd     = in_pcap.rsvd;
    pcc_fullcap.addr     = addr;

    pcc_fullcap.top_cor  = 2'b0;          // will be updated by set_address()
    pcc_fullcap.base_cor = 1'b0;

    pcc_fullcap.perms    = in_pcap.perms;
    pcc_fullcap.top33    = in_pcap.top33;
    pcc_fullcap.base32   = in_pcap.base32;
 
    pcc_fullcap  = set_address(pcc_fullcap, addr);  // check representability
    return pcc_fullcap;
  endfunction

  // coversion without set_address check
  function automatic full_cap_t pcc2fullcap_lite (pcc_cap_t in_pcap, logic [31:0] addr);
    full_cap_t   pcc_fullcap;
    logic [8:0]  top9, base9;

    top9      = TOP_W'(in_pcap.top33  >> (in_pcap.exp));
    base9     = BOT_W'(in_pcap.base32 >> (in_pcap.exp));

    pcc_fullcap.valid    = in_pcap.valid;   
    pcc_fullcap.exp      = in_pcap.exp; 
    pcc_fullcap.top9     = top9;
    pcc_fullcap.base9    = base9;
    pcc_fullcap.cperms   = in_pcap.cperms;
    pcc_fullcap.otype    = in_pcap.otype;
    pcc_fullcap.rsvd     = in_pcap.rsvd;
    pcc_fullcap.addr     = addr;

    pcc_fullcap.top_cor  = 2'b0;          // will be updated by set_address_lite()
    pcc_fullcap.base_cor = 1'b0;

    pcc_fullcap.perms    = in_pcap.perms;
    pcc_fullcap.top33    = in_pcap.top33;
    pcc_fullcap.base32   = in_pcap.base32;
 
    return pcc_fullcap;
  endfunction

  // compress full_cap to pcc_cap
  function automatic pcc_cap_t full2pcap (full_cap_t full_cap);
    pcc_cap_t pcc_cap;

    pcc_cap.valid    = full_cap.valid;
    pcc_cap.exp      = full_cap.exp;
    pcc_cap.top33    = full_cap.top33;
    pcc_cap.base32   = full_cap.base32;
    pcc_cap.otype    = full_cap.otype;
    pcc_cap.perms    = full_cap.perms;
    pcc_cap.cperms   = full_cap.cperms;
    pcc_cap.rsvd     = full_cap.rsvd;

    return pcc_cap;
  endfunction

  function automatic reg_cap_t pcc2regcap (pcc_cap_t pcc_cap, logic [31:0] address, logic clrtag);
    reg_cap_t  reg_cap;
    full_cap_t tfcap0;

    tfcap0  = pcc2fullcap(pcc_cap, address);
    
    reg_cap = RegCapW'(tfcap0);
    if (clrtag) reg_cap.valid = 1'b0;

    return reg_cap;
  endfunction

  //
  // pack/unpack the cap+addr between reg and memory
  // format 0: lsw32 = addr, msw33 = cap fields
  //

  function automatic reg_cap_t mem2regcap(mem_cap_t mem_cap, logic [3:0] clrperm);   
    reg_cap_t         reg_cap;
    logic             sealed;
    logic             denorm, ltop, btop, ttop, tcin; 
    logic [EXP_W-1:0] cexp;
    logic [7:0]       top8, base8;

    cexp   = mem_cap.cexp;
    denorm = (cexp == 0);
    btop   = mem_cap.base9[8];
    base8  = mem_cap.base9[7:0];
    top8   = mem_cap.top8;

    tcin   = (top8 < base8);           // can actually merge it with t_hi in update_temp_fields QQQ
    ltop   = ~denorm;
    ttop   = ltop ^ tcin ^ btop;
    
    sealed = (mem_cap.otype != OTYPE_UNSEALED);

    reg_cap.rsvd   = mem_cap.rsvd;
    reg_cap.otype  = mem_cap.otype;
    reg_cap.exp    =  cexp ^ {5{~denorm}};      // this is the ^0b11111 part (map cexp==31 to exp==0 in norm case
    reg_cap.top9   = {ttop, mem_cap.top8};    // 9-bit
    reg_cap.base9  = mem_cap.base9;
    reg_cap.addr   = mem_cap.addr;
   
    reg_cap.valid  = mem_cap.valid & ~clrperm[3];   
    reg_cap.cperms = mask_clcperms(mem_cap.cperms, clrperm, reg_cap.valid, sealed);
    
    return reg_cap;
  endfunction
  
  function automatic mem_cap_t op2memcap(op_cap_t op_cap);   
    mem_cap_t mem_cap;
    logic        denorm, ltop, cor;
    logic  [9:0] top10, base10, len10;

    cor    = (op_cap.top_cor == {2{op_cap.base_cor}}); 
    top10  = {~cor, op_cap.top9};
    base10 = {1'b0, op_cap.base9};
    len10  = top10 - base10; 
    ltop   = len10[9] | len10[8];

    denorm = (op_cap.exp == 0) && ~ltop;

    mem_cap.valid  = op_cap.valid;
    mem_cap.rsvd   = op_cap.rsvd;
    mem_cap.cperms = op_cap.cperms;
    mem_cap.otype  = op_cap.otype;
    mem_cap.cexp   = op_cap.exp ^ {5{~denorm}};
    mem_cap.top8   = top10[7:0];
    mem_cap.base9  = op_cap.base9;
    mem_cap.addr   = op_cap.addr;

    return mem_cap;
  endfunction

  function automatic op_cap_t reg2opcap (reg_cap_t reg_cap);   // IT8
    op_cap_t op_cap;
    logic [EXP_W-1:0] cexp;
    logic [TOP_W-2:0] top8, base8;
    logic [TOP_W-1:0] top9, base9;
    logic             top_hi, addr_hi;
    logic [BOT_W-1:0] addrmi9;

    op_cap[RegCapW-1:0] = reg_cap;

    top9     = reg_cap.top9;
    base9    = reg_cap.base9;
    addrmi9  = BOT_W'({1'b0, reg_cap.addr} >> op_cap.exp); // ignore the tag valid bit

    top_hi   = (top9 < base9); 
    addr_hi  = (addrmi9 < base9);

    op_cap.top_cor  = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);
    op_cap.base_cor = (addr_hi) ? 1'b1 : 1'b0;

    return op_cap;

  endfunction


  // op to reg, simple truncation
  function automatic reg_cap_t op2regcap(op_cap_t op_cap);    
    reg_cap_t reg_cap;

    reg_cap = op_cap[RegCapW-1:0];

    return reg_cap;
  endfunction

  // for trace file compatibility only, convert the reg (IT8) format to 
  // the non-IT8 memory format.
  function automatic logic[32:0] trace_reg_fmt (reg_cap_t reg_cap);
    op_cap_t     op_cap;       
    mem_cap_t    mem_cap;

    logic [32:0] msw, msw2;

    op_cap      = reg2opcap(reg_cap);

    // tranlate to the "canonical" format
    msw[32]     = op_cap.valid;
    msw[31]     = op_cap.rsvd;
    msw[30:25]  = op_cap.cperms;
    msw[24:22]  = op_cap.otype;
    msw[21:18]  = (op_cap.exp == 24) ? 4'hf : op_cap.exp[3:0];
    msw[17:9]   = op_cap.top9;
    msw[8:0]    = op_cap.base9;

    // "raw" format (as seen in the actual memory)
    mem_cap  = op2memcap(op_cap);
    msw2     = mem_cap[64:32];
    // return msw;
    return msw2;

  endfunction

  function automatic logic[32:0] trace_mem_fmt (mem_cap_t mem_cap);
    logic [32:0] msw;

    msw  = trace_reg_fmt(mem2regcap(mem_cap, 0));
    return msw;
  endfunction


  // 
  function automatic op_cap_t and_opcap_tag (op_cap_t in_cap, logic tag_mask);
    op_cap_t out_cap;

    out_cap = in_cap;
    out_cap.valid = in_cap.valid & tag_mask;
    return out_cap;

  endfunction

  // parameters and constants

  parameter logic[6:0] CHERI_INSTR_OPCODE = 7'h5b;
  parameter int OPDW = 36;      // Must >= number of cheri operator/instructions we support

  typedef enum logic [5:0] {
    CGET_PERM        = 6'h00,
    CGET_TYPE        = 6'h01,
    CGET_BASE        = 6'h02,
    CGET_LEN         = 6'h03,
    CGET_TAG         = 6'h04,
    CGET_TOP         = 6'h05,
    CGET_HIGH        = 6'h06,
    CGET_ADDR        = 6'h07,
    CSEAL            = 6'h08,
    CUNSEAL          = 6'h09,
    CAND_PERM        = 6'h0a,
    CSET_ADDR        = 6'h0b,
    CINC_ADDR        = 6'h0c,
    CINC_ADDR_IMM    = 6'h0d,
    CSET_BOUNDS      = 6'h0e,
    CSET_BOUNDS_EX   = 6'h0f,
    CSET_BOUNDS_IMM  = 6'h10,
    CIS_SUBSET       = 6'h11,
    CIS_EQUAL        = 6'h12,
    CMOVE_CAP        = 6'h13,
    CSUB_CAP         = 6'h14,
    CCLEAR_TAG       = 6'h15,
    CLOAD_CAP        = 6'h16,
    CSET_HIGH        = 6'h17,
    CSTORE_CAP       = 6'h18,
    CCSR_RW          = 6'h19,
    CJALR            = 6'h1a,
    CJAL             = 6'h1b,
    CAUIPCC          = 6'h1c,
    CAUICGP          = 6'h1d,
    CRRL             = 6'h1e,
    CRAM             = 6'h1f,
    CSET_BOUNDS_RNDN = 6'h20
  } cheri_op_e;

  typedef enum logic [4:0] {
    CHERI_CSR_NULL,
    CHERI_CSR_RW
  } cheri_csr_op_e;

  parameter logic [4:0] CHERI_SCR_MEPCC      = 5'd31;
  parameter logic [4:0] CHERI_SCR_MSCRATCHC  = 5'd30;
  parameter logic [4:0] CHERI_SCR_MTDC       = 5'd29;
  parameter logic [4:0] CHERI_SCR_MTCC       = 5'd28;
  parameter logic [4:0] CHERI_SCR_ZTOPC      = 5'd27;
  parameter logic [4:0] CHERI_SCR_DSCRATCHC1 = 5'd26;
  parameter logic [4:0] CHERI_SCR_DSCRATCHC0 = 5'd25;
  parameter logic [4:0] CHERI_SCR_DEPCC      = 5'd24;

  // permission violations
  parameter int unsigned PVIO_W = 8;

  parameter logic [2:0] PVIO_TAG   = 3'h0;
  parameter logic [2:0] PVIO_SEAL  = 3'h1;
  parameter logic [2:0] PVIO_EX    = 3'h2;
  parameter logic [2:0] PVIO_LD    = 3'h3;
  parameter logic [2:0] PVIO_SD    = 3'h4;
  parameter logic [2:0] PVIO_SC    = 3'h5;
  parameter logic [2:0] PVIO_ASR   = 3'h6;
  parameter logic [2:0] PVIO_ALIGN = 3'h7;
  

  function automatic logic [4:0] vio_cause_enc (logic bound_vio, logic[PVIO_W-1:0] perm_vio_vec);
    logic [4:0] vio_cause;
    
    if (perm_vio_vec[PVIO_TAG])
      vio_cause = 5'h2;
    else if (perm_vio_vec[PVIO_SEAL])
      vio_cause = 5'h3;
    else if (perm_vio_vec[PVIO_EX])
      vio_cause = 5'h11;
    else if (perm_vio_vec[PVIO_LD])
      vio_cause = 5'h12;
    else if (perm_vio_vec[PVIO_SD])
      vio_cause = 5'h13;
    else if (perm_vio_vec[PVIO_SC])
      vio_cause = 5'h15;
    else if (perm_vio_vec[PVIO_ASR])
      vio_cause = 5'h18;
    else if (bound_vio)
      vio_cause = 5'h1;
    else
      vio_cause = 5'h0;

    return vio_cause;
  endfunction

  //
  // new stuff..
  //
  typedef struct packed {
    logic               cs1_valid;
    logic [32:0]        cs1_top33;
    logic [31:0]        cs1_base32;
    logic [PERMS_W-1:0] cs1_perms;
    logic [OTYPE_W-1:0] cs1_otype;
    logic               cs2_valid;
    logic [PERMS_W-1:0] cs2_perms;
  } cheri_lschk_info_t;
 
  parameter cheri_lschk_info_t NULL_LSCHK_INFO = '{0, 0, 0, 0, 0, 0, 0};

  function automatic cheri_lschk_info_t build_lschk_info (full_cap_t cs1_fcap, full_cap_t cs2_fcap);
    cheri_lschk_info_t result;

    result.cs1_valid  = cs1_fcap.valid;
    result.cs1_top33  = cs1_fcap.top33;
    result.cs1_base32 = cs1_fcap.base32;
    result.cs1_perms  = cs1_fcap.perms;
    result.cs1_otype  = cs1_fcap.otype;
    result.cs2_valid  = cs2_fcap.valid;
    result.cs2_perms  = cs2_fcap.perms;
    
    return result;
  endfunction

  function automatic logic [7:0] cheri_ls_check (cheri_lschk_info_t lschk_info, 
                                                 logic [31:0] mem_addr, logic is_load, 
                                                 logic is_cap, logic [1:0] data_type);   
    logic [7:0]  result;    
    logic [31:0] top_offset;
    logic [32:0] top_bound;
    logic [31:0] base_bound, base_chkaddr;
    logic [32:0] top_chkaddr;
    logic        top_size_ok;
    logic        is_load_cap, is_store_cap;
    logic        top_vio, base_vio, top_equal;
    logic        cheri_perm_vio, cheri_bound_vio;
    logic [PVIO_W-1:0] perm_vio_vec;
    logic        perm_vio_slc;
    logic [4:0]  cheri_vio_cause;
    logic        addr_bound_vio_ext;
    logic [32:0] cheri_top_chkaddr_ext;
    logic        align_err_only;

    //
    // cheri address bound violation
    //

    // generate the address used to check top bound violation
    base_chkaddr = mem_addr;     // cs1.address + offset

    if (is_cap)  // CLC/CSC
      top_chkaddr = {1'b0, base_chkaddr[31:3], 3'b000};
    else 
      top_chkaddr = {1'b0, base_chkaddr};

    base_bound = lschk_info.cs1_base32;

    if (is_cap) begin // CLC/CSC
      top_bound   = {lschk_info.cs1_top33[32:3], 3'b000};       // 8-byte aligned access only
      top_size_ok = 1'b1;
    end else begin
      case (data_type)
        2'b00: begin
            top_offset  = 32'h4;
            top_size_ok = |lschk_info.cs1_top33[32:2];     // at least 4 bytes
          end
        2'b01: begin
            top_offset  = 32'h2;
            top_size_ok = |lschk_info.cs1_top33[32:1];
          end
        default: begin
            top_offset  = 32'h1;
            top_size_ok = |lschk_info.cs1_top33[32:0];
          end
      endcase

      top_bound = lschk_info.cs1_top33 - top_offset;
    end

    top_vio   = (top_chkaddr  > top_bound) || ~top_size_ok;
    base_vio  = (base_chkaddr < base_bound);
    top_equal = (top_chkaddr == top_bound);

    cheri_bound_vio = (top_vio | base_vio | (is_cap & top_equal));

    //
    // cheri permission violation
    //

    is_load_cap  = is_cap & is_load;
    is_store_cap = is_cap & ~is_load;

    perm_vio_vec = '0;
    perm_vio_slc = 1'b0;

    if (is_load_cap) begin
      perm_vio_vec[PVIO_TAG]   = ~lschk_info.cs1_valid;
      perm_vio_vec[PVIO_SEAL]  = (lschk_info.cs1_otype != OTYPE_UNSEALED);
      perm_vio_vec[PVIO_LD]    = ~(lschk_info.cs1_perms[PERM_LD]);
      perm_vio_vec[PVIO_ALIGN] = (mem_addr[2:0] != 0);
    end else if (is_store_cap) begin
      perm_vio_vec[PVIO_TAG]   = (~lschk_info.cs1_valid);
      perm_vio_vec[PVIO_SEAL]  = (lschk_info.cs1_otype != OTYPE_UNSEALED);
      perm_vio_vec[PVIO_SD]    = ~lschk_info.cs1_perms[PERM_SD];
      perm_vio_vec[PVIO_SC]    = (~lschk_info.cs1_perms[PERM_MC] && lschk_info.cs2_valid);
      perm_vio_vec[PVIO_ALIGN] = (mem_addr[2:0] != 0);
      perm_vio_slc             = ~lschk_info.cs1_perms[PERM_SL] && lschk_info.cs2_valid &&
                                 ~lschk_info.cs2_perms[PERM_GL] ;
    end else begin  // RV32 accesses
      perm_vio_vec[PVIO_TAG]   = ~lschk_info.cs1_valid;
      perm_vio_vec[PVIO_SEAL]  = (lschk_info.cs1_otype != OTYPE_UNSEALED);
      perm_vio_vec[PVIO_LD]    = is_load & ~lschk_info.cs1_perms[PERM_LD];
      perm_vio_vec[PVIO_SD]    = ~is_load && ~lschk_info.cs1_perms[PERM_SD];
    end

    cheri_perm_vio  = | perm_vio_vec;

    cheri_top_chkaddr_ext = mem_addr + 8;   // extend to 33 bit for compare
    addr_bound_vio_ext = is_cap ? cheri_bound_vio | (cheri_top_chkaddr_ext > lschk_info.cs1_top33) :
                                  cheri_bound_vio;

    cheri_vio_cause = vio_cause_enc(addr_bound_vio_ext, perm_vio_vec);
    align_err_only = perm_vio_vec[PVIO_ALIGN] &  (perm_vio_vec[PVIO_ALIGN-1:0] == 0) && ~addr_bound_vio_ext;

    result = {cheri_vio_cause, align_err_only, perm_vio_slc, (cheri_bound_vio|cheri_perm_vio)};
    return result;
  endfunction

endpackage
