// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_rvfi_seq_item extends uvm_sequence_item;
  bit        intr;
  bit        trap;

  bit [4:0]  rd_addr;
  bit [4:0]  rs1_addr;
  bit [4:0]  rs2_addr;

  bit [3:0]  mem_wmask;
  bit [3:0]  mem_rmask;
  bit [31:0] mem_wdata;
  bit [31:0] mem_rdata;
  bit [31:0] mem_addr;

  bit [31:0] rd_wdata;
  bit [31:0] rs1_data;
  bit [31:0] rs2_data;

  bit [31:0] insn;
  bit [31:0] pc;
  bit [31:0] pc_wdata;

  bit [63:0] order;

  bit [31:0] mip;
  bit        nmi;
  bit        debug_req;
  bit [63:0] mcycle;

  `uvm_object_utils_begin(ibex_rvfi_seq_item)
    `uvm_field_int(rd_addr, UVM_DEFAULT)
    `uvm_field_int(rs1_addr, UVM_DEFAULT)
    `uvm_field_int(rs2_addr, UVM_DEFAULT)
    `uvm_field_int(mem_wmask, UVM_DEFAULT)
    `uvm_field_int(mem_rmask, UVM_DEFAULT)
    `uvm_field_int(mem_wdata, UVM_DEFAULT)
    `uvm_field_int(mem_rdata, UVM_DEFAULT)
    `uvm_field_int(mem_addr, UVM_DEFAULT)

    `uvm_field_int(rd_wdata, UVM_DEFAULT)
    `uvm_field_int(rs1_data, UVM_DEFAULT)
    `uvm_field_int(rs2_data, UVM_DEFAULT)

    `uvm_field_int(insn, UVM_DEFAULT)
    `uvm_field_int(pc, UVM_DEFAULT)
    `uvm_field_int(pc_wdata, UVM_DEFAULT)

    `uvm_field_int(order, UVM_DEFAULT)

    `uvm_field_int (mip, UVM_DEFAULT)
    `uvm_field_int (mcycle, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : ibex_rvfi_seq_item
