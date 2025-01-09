# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# CHERIoT Sail model with changes for Ibex
{
  pkgs,
  src,
}:

pkgs.sail-riscv-rv32.overrideAttrs {
  pname = "lowrisc_cheriot_sail";
  inherit src;

  # The upstream patches does not apply to our older version of riscv_sail.
  patches = [ ];
}
