Please follow the steps below to build test images and run VCS simulation. Note the vcs filelists and script may have to be modified to reflect your setup.

### Compile coremark test for RV32IMC
1. cd tests
2. ../scripts/build_coremark_rv32.sh
The scripts genearates a 64-bit hex (coremark.rv32o3.vhx) file and place it in sim/run/bin and other files (.dis, .bin, .elf, etc) in sim/tests/work. 

### Compile coremark test for CHERIoT
1. cd tests
2. ../scripts/build_coremark.sh
The scripts genearates a 64-bit hex (coremark.cheriot.vhx) file and place it in sim/run/bin and other files (.dis, .bin, .elf, etc) in sim/tests/work. 

### Run VCS simulation with cheriot-kudu
1. cd run
2. use ./vcscomp to compile RTL and testbench in CHERIoT mode, or use ./vcscomp32 to compile in RV32 mode
3. ./simv +TEST=testname, where testname must correspond to a vhx file in bin/directory
   - e.g. ./simv +TEST=coremark.cheriot
     
### Run VCS simulation with cheriot-ibex 
1. cd run_ibex
2. create a symbolic link to ../run/bin
3. use ./vcsibex to compile RTL and testbench in CHERIoT mode, or use ./vcsibex32 to compile in RV32 mode
4. ./simv +TEST=testname, where testname must correspond to a vhx file in bin/directory
   
