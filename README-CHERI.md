### Compilation:
  - ifdef's: to enable trace generation for simulation, +define+RVFI. no other ifdef's needed
  - top-level design: ibex_top_tracing 

### List of design files

Core RTL files:
-  $rtl/ibex_pkg.sv
-  $rtl/cheri_pkg.sv
-  $rtl/cheri_decoder.sv
-  $rtl/cheri_ex.sv
-  $rtl/cheri_regfile.sv
-  $rtl/cheri_trvk_stage.sv
-  $rtl/cheri_tbre.sv
-  $rtl/cheri_stkz.sv
-  $rtl/cheri_tbre_wrapper.sv
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
-  $rtl/ibex_pmp.sv
-  $rtl/ibex_prefetch_buffer.sv
-  $rtl/ibex_tracer.sv
-  $rtl/ibex_tracer_pkg.sv
-  $rtl/ibex_wb_stage.sv

To compile a simple top-level (without security options), use
-  $rtl/ibexc_top.sv
-  $rtl/ibexc_top_tracing.sv
  
To compile the full ibex top-level, use
- $rtl/ibex_core.sv
- $rtl/ibex_lockstep.sv
- $rtl/ibex_register_file_ff.sv
- $rtl/ibex_pmp.sv
- $rtl/ibex_top.sv
- $rtl/ibex_tracer.sv
- $rtl/ibex_top_tracing.sv


### Dependencies
-  dv_fcov_macros.svh 
-  prim_cipher_pkg.sv
-  prim_lfsr.sv
-  prim_ram_1p_pkg.sv
-  prim_assert.sv
-  prim_assert_dummy_macros.svh
-  prim_assert_standard_macros.svh
-  prim_secded_pkg.sv
-  prim_secded_inv_39_32_dec.sv
-  prim_secded_inv_39_32_enc.sv
-  prim_buf.sv
-  prim_flop.sv
-  prim_clock_mux2.sv
-  prim_clock_gating.sv
