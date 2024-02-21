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
    logic [32:0]   wdata;
    logic [32:0]   rdata;
    logic          err;
  } mem_cmd_t;

  typedef struct packed {
    logic        is_cap;
    logic        we;
    logic [1:0]  rv32_type;
    logic [31:0] addr;
    reg_cap_t    wcap;
    logic [31:0] wdata;
    reg_cap_t    rcap;
    logic [31:0] rdata;
    logic        err;
  } lsu_cmd_t;

endpackage
