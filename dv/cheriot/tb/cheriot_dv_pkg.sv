// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cheriot_dv_pkg;
  import cheri_pkg::*;

  parameter logic [31:0] DRAMStartAddr  = 32'h8000_0000;
  parameter logic [31:0] TsMapStartAddr = 32'h8300_0000;

  typedef struct packed {
    logic [7:0]    flag;
    logic          is_cap;
    logic          we;
    logic [3:0]    be;
    logic [29:0]   addr32;
    logic [64:0]   wdata;
    logic [64:0]   rdata;
    logic          err;
  } mem_cmd_t;

  typedef struct packed {
    logic        is_cap;
    logic        is_raw;
    logic        we;
    logic [1:0]  rv32_type;
    logic [31:0] addr;
    reg_cap_t    wcap;
    logic [31:0] wdata;
    reg_cap_t    rcap;
    logic [31:0] rdata;
    logic [64:0] raw_wdata;
    logic [64:0] raw_rdata;
    logic        err;
  } lsu_cmd_t;

  function automatic logic is_representable(full_cap_t in_cap, logic [31:0] address);
    logic        result;
    logic [32:0] rep_top;

    rep_top = 33'h1 << (9+in_cap.exp);

    if (in_cap.exp == 24) 
      result = 1'b1;
    else if ((address >= in_cap.base32) && ((address - in_cap.base32) < rep_top))
      result = 1'b1;
    else 
      result = 1'b0;

    return result;
  endfunction

  function automatic logic[2:0] repr_cases (full_cap_t in_cap, logic [31:0] address);
    logic [2:0]  result;
    logic [32:0] rep_top;

    rep_top = 33'h1 << (9+in_cap.exp);

    // error cases to be covered, will add more later
    if (address < in_cap.base32)
      result = 1;
    else if ((address - in_cap.base32) >= rep_top)
      result = 2;
    else 
      result = 0;

    return result;
  endfunction

  function automatic logic[5:0] count32_zeros (logic [31:0] address);
    logic [5:0]  result;
    int i;

    result = 0;
    for (i = 0; i <=31; i++)
      if (address[i] == 1'b0) result += 1;

    return result;
  endfunction

  function automatic logic[8:0] bound_check_cases (full_cap_t in_cap, logic [31:0] address);
    logic [8:0]  result;
    logic [33:0] room;

    result[0] = (address <  in_cap.base32);    // impossible value = 2'b11
    result[1] = (address == in_cap.base32);

    result[2] = (address >  in_cap.top33);     // impossible value = 2'b11
    result[3] = (address == in_cap.top33);

    /*
     * base32 is always <= top33, so also impossible:
     * 4'b?1?1: can't be below    base and above    top
     * 4'b?11?: can't be equal to base and above    top
     * 4'b1??1: can't be below    base and equal to top
     */

    room = in_cap.top33 - address;
    if ((room > 0) && (room < 8)) result[6:4] = room[2:0];
    else result[6:4] = 0;

    /*
     * Bits [6:4] are nonzero only when the address is just below the top.
     * So, also impossible are...
     * 7'b??1_?1??: can't be both below and above    the top
     * 7'b?1?_?1??: ditto
     * 7'b1??_?1??: ditto
     * 7'b??1_1???: can't be both below and equal to the top
     * 7'b?1?_1???: ditto
     * 7'b1??_1???: ditto
     */

    // cornercases 
    result[7] = (in_cap.top33  == 33'h1_0000_0000);
    result[8] = (in_cap.base32 == 33'h0);

    /*
     * Address is >= 0, and so 9'b1_????_???1 is impossible, as if the base is
     * 0, the address surely cannot be below it.
     */

    return result;
  endfunction

  `define bound_check_cases_ignore_bins \
      wildcard ignore_bins ignore_base    = {9'b?_????_??11}; \
      wildcard ignore_bins ignore_top     = {9'b?_????_11??}; \
      wildcard ignore_bins ignore_range_0 = {9'b?_????_?1?1}; \
      wildcard ignore_bins ignore_range_1 = {9'b?_????_?11?}; \
      wildcard ignore_bins ignore_range_2 = {9'b?_????_1??1}; \
      wildcard ignore_bins ignore_room_0  = {9'b?_???1_?1??}; \
      wildcard ignore_bins ignore_room_1  = {9'b?_??1?_?1??}; \
      wildcard ignore_bins ignore_room_2  = {9'b?_?1??_?1??}; \
      wildcard ignore_bins ignore_room_3  = {9'b?_???1_1???}; \
      wildcard ignore_bins ignore_room_4  = {9'b?_??1?_1???}; \
      wildcard ignore_bins ignore_room_5  = {9'b?_?1??_1???}; \
      wildcard ignore_bins ignore_below0  = {9'b1_????_???1};

  function automatic logic[4:0] setbounds_cases (full_cap_t cs1_cap, logic [31:0] cs1_address, logic [31:0] req_len);
    logic [4:0]  result;

    logic [32:0] cs1_len;

    result[0] = (cs1_address <  cs1_cap.base32);    // impossible value = 2'b11
    result[1] = (cs1_address == cs1_cap.base32);
    
    result[2] = (cs1_address >  cs1_cap.top33);     // impossible value = 2'b11
    result[3] = (cs1_address == cs1_cap.top33);

    cs1_len = cs1_cap.top33 - cs1_cap.base32;
    result[4] = (req_len <= cs1_len);

    return result;
  endfunction

  function automatic full_cap_t mem2fullcap_fmt0_raw (logic [32:0] msw, logic [32:0] addr33);
    reg_cap_t  regcap;
    full_cap_t result_cap;

    logic [EXP_W-1:0] tmp5;
    logic [3:0]  tmp4;
    logic [CPERMS_W-1:0] cperms_mem;
    logic [BOT_W-1:0]    addrmi9;
    logic                valid_in;

    valid_in      = msw[32] & addr33[32];
    regcap.valid  = valid_in;   

    tmp5 = {1'b0, msw[CEXP_LO+:CEXP_W]};
    if (tmp5 == EXP_W'(RESETCEXP)) tmp5 = RESETEXP;
    regcap.exp = tmp5;

    regcap.top    = msw[TOP_LO+:TOP_W];
    regcap.base   = msw[BASE_LO+:BOT_W];
    regcap.otype  = msw[OTYPE_LO+:OTYPE_W];

    cperms_mem      = msw[CPERMS_LO+:CPERMS_W];
    regcap.cperms   = cperms_mem;
    addrmi9         = BOT_W'({1'b0, addr33[31:0]} >> regcap.exp); // ignore the tag valid bit
    tmp4            = update_temp_fields(regcap.top, regcap.base, addrmi9);
    regcap.top_cor  = tmp4[3:2];
    regcap.base_cor = tmp4[1:0];

    regcap.rsvd     = msw[RSVD_LO];

    result_cap      = reg2fullcap(regcap, addr33[31:0]);

    return result_cap;

  endfunction

endpackage
