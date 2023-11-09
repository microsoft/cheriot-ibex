This is the experimental cheriot verification setup. The idea is to 
  - use a CHERIoT-aware tool (TestRIG-like) to generate a (constrained) random instruction stream
  - execute the instruction stream with both cheriot-sail and cheriot-ibex RTL & testbench
  - Compare the trace file from sail and ibex
  - In addition, the cheriot-ibex testbench will support
    - randomized memory interface/interrupt timing
    - additional checkers/assertions/monitors to ensure microarchitectural states and memory transactions are consistent

Currently we support the following RTL simulation setups
  - Verilator with a instruction stream file (instructions in hex format)
    - cd run/
    - ./vgen
    - ./vcomp
    - ./obj_dir/Vtb_cheriot_top input_file 
  - VCS with a instruction stream file
    - cd run/
    - ./vcscomp           &nbsp;&nbsp;&nbsp;&nbsp; &nbsp;&nbsp;&nbsp;&nbsp; // ./bin/instr_stream.vhx contains the pre-generated instruction stream
    - ./simv
  - VCS with an ELF
    - ./vcscomp2          
    - ./simv              &nbsp;&nbsp;&nbsp;&nbsp; &nbsp;&nbsp;&nbsp;&nbsp; // ./bin/instr_mem.vhx contains the pre-generated memory image
   
scripts/compare_trace.py is a python script which can be used to compare ibex and sail trace files
  - ../scripts/compare_trace.py ibex_trace_file_Name sail_trace_file_name

For an example of the instruction stream file format, see run/bin/instr_stream_example.vhx
