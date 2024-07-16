This folder contains a verilator simulation which will connect to TestRIG, so
that it can receive instructions over the input socket and output the RVFI
traces on the output socket.

Currently this passes the arithmetic, memory, control flow, cache, mult/div,
"all", and "random" generators when run against the Sail-RISCV model with
TestRIG, with the following caveats:
- Ibex does not support S mode, so SRET instructions should not be generated.
- Ibex supports unaligned accesses, so it cannot be run against cores that do
  not support this (the Sail-RISCV model supports this when
  "--support-misaligned" is passed as an argument to the TestRIG script).
- Compressed instructions appear to not be working correctly -- this has not yet
  been looked at.
