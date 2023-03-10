### Compilation:
  - ifdef's: to enable trace generation for simulation, +define+RVFI. no other ifdef's needed
  - top-level design: ibex_top_tracing (in ibexc_top_tracing.sv)

### Recommended top-level parameter settings:
  - Cheri32E = 1'b0
  - CheriPPLBC = 1'b1
  - CheriSBND2 = 1'b0
  - All other parameters at default

### List of design files
-  $rtl/cheri_decoder.sv
-  $rtl/cheri_ex.sv
-  $rtl/cheri_pkg.sv
-  $rtl/cheri_regfile.sv
-  $rtl/cheri_trvk_stage.sv
-  $rtl/ibex_alu.sv
-  $rtl/ibex_branch_predict.sv
-  $rtl/ibex_compressed_decoder.sv
-  $rtl/ibex_controller.sv
-  $rtl/ibex_core.sv
-  $rtl/ibex_counter.sv
-  $rtl/ibex_csr.sv
-  $rtl/ibex_cs_registers.sv
-  $rtl/ibex_decoder.sv
-  $rtl/ibex_dummy_instr.sv
-  $rtl/ibex_ex_block.sv
-  $rtl/ibex_fetch_fifo.sv
-  $rtl/ibex_id_stage.sv
-  $rtl/ibex_if_stage.sv
-  $rtl/ibex_load_store_unit.sv
-  $rtl/ibex_multdiv_fast.sv
-  $rtl/ibex_multdiv_slow.sv
-  $rtl/ibex_pkg.sv
-  $rtl/ibex_pmp.sv
-  $rtl/ibex_prefetch_buffer.sv
-  $rtl/ibex_tracer.sv
-  $rtl/ibex_tracer_pkg.sv
-  $rtl/ibex_wb_stage.sv
-  $rtl/ibexc_top.sv
-  $rtl/ibexc_top_tracing.sv

### Dependencies
-  dv_fcov_macros.svh 
-  prim_cipher_pkg.sv
-  prim_lfsr.sv
-  prim_ram_1p_pkg.sv
-  prim_assert.sv
-  prim_assert_dummy_macros.svh
-  prim_assert_standard_macros.svh
