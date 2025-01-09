# End to End Formal Verification against the Sail

This is very much a WIP. It is however mostly just a CHERI version of the almost exactly identical work for Ibex.
All properties are believed to be conclusive, including wrap around. There is currently no liveness.

Prerequisities (in your PATH):
- [The lowRISC fork of the Sail compiler](https://github.com/lowRISC/sail/tree/lowrisc)
- [psgen](https://github.com/mndstrmr/psgen)
- Nix (`https://zero-to-nix.com/start/install`)
- JasperGold

Build instructions:
- `git submodule init`
- `make psgen` to build the SV for the proofs given in `thm/`
- `make sv` to build the SV translation of the Sail compiler. Will invoke `buildspec.py`, which can be configured to adjust which instructions are defined. By default all of them are, this is correct but slow.
- Make the changes to Ibex described in the RTL changes.
- `SAIL_DIR=<path to sail compiler source> jg verify.tcl`

Nix build instructions:
- Clone this repository
- `cd dv/formal`
- `nix develop .#formal`
- `make` invokes JasperGold in batch-mode, and attempts to prove everything, which is meant for regressions.
- `make jg` invokes JasperGold interactively, halting after sourcing the contents of `verify.tcl`.

You can see the different steps of the proof in the `Task Tree` tab.
Then, you can prove each step in order by right clicking on them and clicking `Prove Task`.
Some tasks may take longer than others and you can select specific properties in the `Property Table` and prove them individually by right clicking and selecting `Prove Property`.
Some steps require a lot of RAM and CPU so we recommend closing any other resource-heavy programs running on your computer.
We've had the proof complete using a machine with 128 GiB of RAM and 32 cores.
To avoid manually running each step you can also use the `prove_no_liveness` command inside the TCL command interface located below your session window.


## RTL Changes
- `ResetAll = 1` is required for now (instead of `ResetAll = Lockstep`)
- Disable clock gating

## Exact Checks
This proves trace equivalence with the Sail as per `cheriot-sail`, note that this is a fork of the original CherIoT-Sail.
This work is very similar to that of Ibex, with the only difference being the inclusion of CHERI instructions. See the Ibex repo for a list of caveats.

Note that in addition to what is listed in the Ibex repo, the following is not covered:
- Stack zeroing (including MSHWM and MSHWMB)
- Reservation/Revocation (see `check/top.sv` for the exact configuration)
