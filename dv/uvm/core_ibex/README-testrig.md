# Overview

Preliminary support for running a lowRISC fork of
[TestRIG](https://github.com/lowRISC/TestRIG/tree/cheriot) against a VCS
simulation of Ibex within a UVM environment is included.

The current support is bare-bones, in particular it does not include a memory
model so memory instructions will not work (the core and simulation will just
lock-up awaiting a grant from the dside memory interface). Nor does it include
support to stimulating interrupts.

To build the simulator binary (once VCS and optionally Verdi have been suitably
setup in your environment), run `testrig_vcs_build.sh` from the
dv/uvm/core_ibex directory. This will build a `simv` simulator binary in
dv/uvm/core_ibex/vcs_testrig_out.

To run TestRIG first follow the instructions in the [TestRIG
README](https://github.com/lowRISC/TestRIG/blob/cheriot/README.md) to setup and
build the TestRIG environment. The VCS simulation support has not been added to
the TestRIG utility scripts yet so the 'manual' implementation type must be
used.

In one shell start the VCS simulation:

```shell
$ ./vcs_testrig_out/simv -ucli -do ./vcs_testrig.tcl +UVM_TESTNAME=core_ibex_testrig_test -l run.log
```

Wait until the simulation has begun listening on port 6000, you should see the
following:

```
UVM_INFO @ 0: reporter [RNTST] Running test core_ibex_testrig_test...
---- allocated socket for RVFI_DII
---- RVFI_DII_PORT environment variable not defined, using default port 6000 instead
---- RVFI_DII socket listening on port 6000
```

In another shell run TestRIG:

```shell
$ utils/scripts/runTestRIG.py -a manual --implementation-A-port 6000 -b sail -r rv32ecZifencei_Xcheriot --test-include-regex '^arith$' --no-shrink --continue-on-fail
```

This will run just the arithmetic tests, which should all pass.

The VCS simulation will terminate on a fatal timeout error as it stops receiving
DII packets from TestRIG. The final few UVM log files should look like this:

```
UVM_INFO /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_dii_driver.sv(84) @ 204284400: uvm_test_top.testrig_env.testrig_agent.dii_driver [uvm_test_top.testrig_env.testrig_agent.dii_driver] Received reset command, inject NOPs until remaining instructions retire
UVM_INFO /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_dii_driver.sv(92) @ 204284400: uvm_test_top.testrig_env.testrig_agent.dii_driver [uvm_test_top.testrig_env.testrig_agent.dii_driver] Seen       2028 instructions in and       2026 instructions out, waiting for the rest
UVM_INFO /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_dii_driver.sv(104) @ 204288400: uvm_test_top.testrig_env.testrig_agent.dii_driver [uvm_test_top.testrig_env.testrig_agent.dii_driver] Performing reset
UVM_INFO /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_agent.sv(90) @ 204288600: uvm_test_top.testrig_env.testrig_agent [uvm_test_top.testrig_env.testrig_agent] Seen reset, sending RVFI halt
UVM_INFO /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_agent.sv(91) @ 204288600: uvm_test_top.testrig_env.testrig_agent [uvm_test_top.testrig_env.testrig_agent]        2028 total RVFI seen,        2028 RVFI send limit
UVM_FATAL /home/greg/work/cheriot-ibex/dv/uvm/core_ibex/common/ibex_testrig_agent/ibex_testrig_dii_driver.sv(72) @ 204294400: uvm_test_top.testrig_env.testrig_agent.dii_driver [uvm_test_top.testrig_env.testrig_agent.dii_driver] Timeout waiting for next DII packet
```

Waves are output in FSDB if Verdi is available or the DVE VPD format. They can
be found in the `waves.fsdb` or `waves.vpd` in the same directory the simulation
was run from.

To get more verbose logging (which includes all instructions injected and all
RVFI packets sent back) set `UVM_VERBOSITY` to `UVM_HIGH`

```shell
$ ./vcs_testrig_out/simv -ucli -do ./vcs_testrig.tcl +UVM_TESTNAME=core_ibex_testrig_test +UVM_VERBOSITY=UVM_HIGH -l run.log
```

Logs are output to stdout as well as written to `run.log`
