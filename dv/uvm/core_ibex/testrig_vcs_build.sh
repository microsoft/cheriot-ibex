#!/bin/bash

export PRJ_DIR=$(realpath ../../../)

mkdir -p vcs_testrig_out

vcs -f ibex_testrig_dv.f -full64 -l vcs_testrig_out/compile.log -sverilog \
  -ntb_opts uvm-1.2 +define+UVM -o vcs_testrig_out/simv -timescale=1ns/10ps \
  -q -cm line+cond+tgl+fsm+branch+assert -cm_dir sim \
  -debug_access+all -CFLAGS "-I${PRJ_DIR}/vendor/SocketPacketUtils"
