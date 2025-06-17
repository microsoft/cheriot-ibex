// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module kudu_top import super_pkg::*;  #(
  parameter bit          CHERIoTEn      = 1'b0,
  parameter bit          DualIssue      = 1'b1,
  parameter bit          EarlyLoad      = 1'b1,
  parameter bit          DCacheEn       = 1'b0,
  parameter bit          TwoStageIR     = 1'b1,
  parameter bit          InstrBufEn     = 1'b1,
  parameter bit          LoadFiltEn     = 1'b1,
  parameter bit          NoMult         = 1'b0,
  parameter bit          UseDWMult      = 1'b0,
  parameter bit          UnalignedFetch = 1'b0,
  parameter int unsigned HeapBase  = 32'h2001_0000,
  parameter int unsigned TSMapSize = 1024
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic                         cheri_pmode_i,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [63:0]                  instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  output logic                         data_is_cap_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemW-1:0]              data_wdata_o,
  input  logic [MemW-1:0]              data_rdata_i,
  input  logic                         data_err_i,

  output logic                         tsmap_cs_o,
  output logic [15:0]                  tsmap_addr_o,
  input  logic [31:0]                  tsmap_rdata_i,
  output logic                         cheri_fatal_err_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i
  );

  import csr_pkg::*;
  import cheri_pkg::*;

  rf_rdata2_t     rf_rdata2_p0;
  rf_rdata2_t     rf_rdata2_p1;
  rf_raddr2_t     rf_raddr2_p0;
  rf_raddr2_t     rf_raddr2_p1;

  op_data2_t      ira_op_rf_rdata2, irb_op_rf_rdata2;

  logic [RegW-1:0] rf_wdata0, rf_wdata1, rf_wdata2;
  logic [4:0]      rf_waddr0, rf_waddr1, rf_waddr2;
  logic            rf_we0, rf_we1, rf_we2;
  logic            fetch_req;       

  // control signals
  logic           ex_pc_set;
  logic [31:0]    ex_pc_target;            // Not-taken branch address in ID/EX
                                            // vectorized interrupt lines
  logic           ex_bp_init;         
  ex_bp_info_t    ex_bp_info;         
                  
  logic [1:0]     ir_rdy;
  ir_reg_t        if_instr0;
  ir_reg_t        if_instr1;
  logic [1:0]     if_valid;
                  
  logic [1:0]     ir_valid;
  logic [1:0]     if_rdy;
  ir_dec_t        ira_dec, irb_dec;
                  
  logic [1:0]     issuer_rdy;
  logic           alupl0_rdy;
  logic           alupl1_rdy;
  logic           lspl_rdy;
  logic           multpl_rdy;
  logic [4:0]     ex_valid;
                  
  logic           lspl_sel_ira;
  logic           multpl_sel_ira;
                  
  logic [31:0]    alupl0_fwd_act, alupl1_fwd_act, lspl_fwd_act,  multpl_fwd_act;
  waw_act_t       waw_act;
  logic           cmt_err;  
  logic [31:0]    cmt_regwr;
  cmt_err_info_t  cmt_err_info;
  logic [1:0]     sbdfifo_wr_valid, sbdfifo_rd_valid;  
  logic [1:0]     sbdfifo_wr_rdy, sbdfifo_rd_rdy;  
  sbd_fifo_t      sbdfifo_wdata0, sbdfifo_wdata1;  
  sbd_fifo_t      sbdfifo_rdata0, sbdfifo_rdata1;  
                  
  logic           alupl0_valid, alupl1_valid, lspl_valid, multpl_valid;
  logic           cmt_alupl0_rdy, cmt_alupl1_rdy, cmt_lspl_rdy, cmt_multpl_rdy;
  logic           cmt_flush;
  pl_fwd_t        alupl0_fwd_info, alupl1_fwd_info, lspl_fwd_info, multpl_fwd_info;
  pl_out_t        alupl0_output, alupl1_output, lspl_output, multpl_output;
                  
  logic [1:0]     branch_valid;
  full_data2_t    ira_full_data2_fwd, irb_full_data2_fwd;
  logic           ira_is0;
                  
  logic [31:0]    ir0_jalr_target,  ir1_jalr_target;
  branch_info_t   branch_info;
  logic [2:0]     ir0_cjalr_err, ir1_cjalr_err;


  logic            csr_access;
  csr_num_e        csr_addr;
  logic [RegW-1:0] csr_wdata;
  csr_op_e         csr_op;
  logic            csr_op_en;
  logic [RegW-1:0] csr_rdata;
  logic            illegal_csr_insn;

  logic            csr_set_mie;
  logic            csr_clr_mie;
                 
  logic            csr_mstatus_tw, csr_mstatus_mie;
                   
  irqs_t           irqs;
  logic            irq_pending;
  logic [31:0]     csr_mtvec;
  logic            csr_mtvec_init;
  logic [31:0]     csr_mepc;
  logic [31:0]     csr_exc_pc;      
  logic            csr_restore_mret;
  logic            csr_restore_dret;
  logic            csr_save_cause;
  logic            csr_mepcc_clrtag;
  exc_cause_e      csr_exc_cause;
  logic [31:0]     csr_mtval;
  logic            csr_cheri;
  logic            csr_lsu_wr_req;
  logic [31:0]     csr_lsu_addr;
                   
  pcc_cap_t        pcc_cap_r, pcc_cap_w;
  logic            cheri_pcc_set;
  logic            trvk_en;
  logic            trvk_clrtag, trvk_outstanding;
  logic [4:0]      trvk_addr;

  regfile #(.NRegs(32)) regfile_i (
     // Clock and Reset
    .clk_i          (clk_i       ),
    .rst_ni         (rst_ni      ),
    .raddr2_p0_i    (rf_raddr2_p0),
    .raddr2_p1_i    (rf_raddr2_p1),
    .rdata2_p0_o    (rf_rdata2_p0),
    .rdata2_p1_o    (rf_rdata2_p1),
    .waddr0_i       (rf_waddr0   ),
    .wdata0_i       (rf_wdata0   ),
    .we0_i          (rf_we0      ),       
    .waddr1_i       (rf_waddr1   ),
    .wdata1_i       (rf_wdata1   ),
    .we1_i          (rf_we1      ),        
    .waddr2_i       (rf_waddr2   ),
    .wdata2_i       (rf_wdata2   ),
    .we2_i          (rf_we2      ),   
    .trvk_en_i      (trvk_en     ), 
    .trvk_clrtag_i  (trvk_clrtag ), 
    .trvk_addr_i    (trvk_addr   )  
  );

  localparam bit IfCompDecEn = ~TwoStageIR;

  if_stage #(
    .CHERIoTEn      (CHERIoTEn),
    .InstrBufEn     (InstrBufEn), 
    .CompDecEn      (IfCompDecEn),
    .UnalignedFetch (UnalignedFetch)
  ) if_stage_i(
    .clk_i                   (clk_i                   ),
    .rst_ni                  (rst_ni                  ),
    .cheri_pmode_i           (cheri_pmode_i           ),
    .req_i                   (fetch_req               ),       
    .debug_mode_i            (1'b0                    ),
    .boot_addr_i             (boot_addr_i             ),
    .instr_req_o             (instr_req_o             ),
    .instr_addr_o            (instr_addr_o            ),
    .instr_gnt_i             (instr_gnt_i             ),
    .instr_rvalid_i          (instr_rvalid_i          ),
    .instr_rdata_i           (instr_rdata_i           ),
    .instr_err_i             (instr_err_i             ),
    .ds_rdy_i                (ir_rdy                  ),
    .if_instr0_o             (if_instr0               ),
    .if_instr1_o             (if_instr1               ),
    .if_valid_o              (if_valid                ),
    .ex_pc_set_i             (ex_pc_set               ),   
    .ex_pc_target_i          (ex_pc_target            ),   
    .ex_bp_init_i            (ex_bp_init              ),
    .ex_bp_info_i            (ex_bp_info              ),
    .if_busy_o               (                        )
  );                        
                           
  ir_stage # (.TwoStage(TwoStageIR), .CHERIoTEn(CHERIoTEn)) ir_stage_i (
    .clk_i              (clk_i           ),
    .rst_ni             (rst_ni          ),
    .cheri_pmode_i      (cheri_pmode_i   ),
    .debug_mode_i       (1'b0            ),
    .pcc_cap_i          (pcc_cap_r       ),
    .us_instr0_i        (if_instr0       ),   
    .us_instr1_i        (if_instr1       ),    
    .us_valid_i         (if_valid        ),
    .ir_rdy_o           (ir_rdy          ),
    .rf_rdata2_p0_i     (rf_rdata2_p0    ),
    .rf_rdata2_p1_i     (rf_rdata2_p1    ),
    .rf_raddr2_p0_o     (rf_raddr2_p0    ),
    .rf_raddr2_p1_o     (rf_raddr2_p1    ),
    .rf_waddr0_i        (rf_waddr0       ),
    .rf_wdata0_i        (rf_wdata0       ),
    .rf_we0_i           (rf_we0          ),       
    .rf_waddr1_i        (rf_waddr1       ),
    .rf_wdata1_i        (rf_wdata1       ),
    .rf_we1_i           (rf_we1          ),        
    .rf_waddr2_i        (rf_waddr2       ),
    .rf_wdata2_i        (rf_wdata2       ),
    .rf_we2_i           (rf_we2          ),   
    .ir_flush_i         (ex_pc_set       ),
    .ds_rdy_i           (issuer_rdy      ),
    .ir_valid_o         (ir_valid        ),
    .ira_is0_o          (ira_is0         ),
    .ira_dec_o          (ira_dec         ),
    .irb_dec_o          (irb_dec         ),
    .ira_op_rf_rdata2_o (ira_op_rf_rdata2),  
    .irb_op_rf_rdata2_o (irb_op_rf_rdata2),
    .trvk_en_i          (trvk_en         ), 
    .trvk_clrtag_i      (trvk_clrtag     ), 
    .trvk_addr_i        (trvk_addr       )  
  );

  issuer #(
    .CHERIoTEn  (CHERIoTEn ), 
    .DualIssue  (DualIssue ), 
    .LoadFiltEn (LoadFiltEn)
  ) issuer_i (
    .clk_i                     (clk_i                   ),
    .rst_ni                    (rst_ni                  ),
    .boot_addr_i               (boot_addr_i             ),
    .cheri_pmode_i             (cheri_pmode_i           ),
    .ira_dec_i                 (ira_dec                 ),
    .irb_dec_i                 (irb_dec                 ),      
    .ira_is0_i                 (ira_is0                 ),
    .ir_valid_i                (ir_valid                ),
    .issuer_rdy_o              (issuer_rdy              ),
    .ira_op_rf_rdata2_i        (ira_op_rf_rdata2        ),
    .irb_op_rf_rdata2_i        (irb_op_rf_rdata2        ),
    .alupl0_rdy_i              (alupl0_rdy              ),
    .alupl0_fwd_info_i         (alupl0_fwd_info         ),
    .alupl1_rdy_i              (alupl1_rdy              ),
    .alupl1_fwd_info_i         (alupl1_fwd_info         ),
    .lspl_rdy_i                (lspl_rdy                ),
    .lspl_fwd_info_i           (lspl_fwd_info           ),
    .multpl_rdy_i              (multpl_rdy              ),
    .multpl_fwd_info_i         (multpl_fwd_info         ),
    .ex_valid_o                (ex_valid                ),
    .lspl_sel_ira_o            (lspl_sel_ira            ),
    .multpl_sel_ira_o          (multpl_sel_ira          ),
    .alupl0_fwd_act_i          (alupl0_fwd_act          ),
    .alupl1_fwd_act_i          (alupl1_fwd_act          ),
    .lspl_fwd_act_i            (lspl_fwd_act            ),
    .multpl_fwd_act_i          (multpl_fwd_act          ),
    .waw_act_o                 (waw_act                 ),
    .cmt_err_i                 (cmt_err                 ),  
    .cmt_err_info_i            (cmt_err_info            ),  
    .cmt_regwr_i               (cmt_regwr               ),
    .cmt_flush_o               (cmt_flush               ),    
    .sbdfifo_rd_valid_i        (sbdfifo_rd_valid        ),
    .sbdfifo_wr_valid_o        (sbdfifo_wr_valid        ),  
    .sbdfifo_wdata0_o          (sbdfifo_wdata0          ),  
    .sbdfifo_wdata1_o          (sbdfifo_wdata1          ),  
    .branch_info_i             (branch_info             ),
    .branch_valid_o            (branch_valid            ),
    .ir0_jalr_target_i         (ir0_jalr_target         ),
    .ir1_jalr_target_i         (ir1_jalr_target         ),
    .ir0_cjalr_err_i           (ir0_cjalr_err           ),
    .ir1_cjalr_err_i           (ir1_cjalr_err           ),
    .ira_full_data2_fwd_o      (ira_full_data2_fwd      ),
    .irb_full_data2_fwd_o      (irb_full_data2_fwd      ),
    .fetch_req_o               (fetch_req               ),
    .pc_set_o                  (ex_pc_set               ),
    .pc_target_o               (ex_pc_target            ),   
    .ex_bp_init_o              (ex_bp_init              ),
    .ex_bp_info_o              (ex_bp_info              ),
    .irq_pending_i             (irq_pending             ),
    .irqs_i                    (irqs                    ),
    .csr_mstatus_mie_i         (csr_mstatus_mie         ),
    .csr_mtvec_i               (csr_mtvec               ),
    .csr_mepc_i                (csr_mepc                ),
    .csr_exc_pc_o              (csr_exc_pc              ),
    .csr_mtvec_init_o          (csr_mtvec_init          ),
    .csr_save_cause_o          (csr_save_cause          ),
    .csr_mepcc_clrtag_o        (csr_mepcc_clrtag        ),
    .csr_restore_mret_o        (csr_restore_mret        ),
    .csr_restore_dret_o        (csr_restore_dret        ),
    .csr_mcause_o              (csr_exc_cause           ),
    .csr_mtval_o               (csr_mtval               ),
    .trvk_en_i                 (trvk_en                 ), 
    .trvk_addr_i               (trvk_addr               ),
    .trvk_outstanding_i        (trvk_outstanding        )
  );
  
  dual_fifo # (.Depth(8), .Width($bits(sbd_fifo_t))) sbd_fifo_i (
    .clk_i       (clk_i            ),
    .rst_ni      (rst_ni           ),
    .flush_i     (cmt_flush        ),
    .wr_valid_i  (sbdfifo_wr_valid ),
    .wr_data0_i  (sbdfifo_wdata0   ),
    .wr_data1_i  (sbdfifo_wdata1   ),
    .wr_rdy_o    (sbdfifo_wr_rdy   ), 
    .rd_rdy_i    (sbdfifo_rd_rdy   ),
    .rd_valid_o  (sbdfifo_rd_valid ),
    .rd_data0_o  (sbdfifo_rdata0   ), 
    .rd_data1_o  (sbdfifo_rdata1   )
  );

  branch_unit #(.CHERIoTEn(CHERIoTEn)) branch_unit_i (
    .clk_i               (clk_i              ), 
    .rst_ni              (rst_ni             ),
    .cheri_pmode_i       (cheri_pmode_i      ),
    .ira_dec_i           (ira_dec            ),
    .irb_dec_i           (irb_dec            ),
    .branch_valid_i      (branch_valid       ),
    .ira_is0_i           (ira_is0            ),
    .ira_full_data2_i    (ira_full_data2_fwd ),
    .irb_full_data2_i    (irb_full_data2_fwd ),
    .branch_info_o       (branch_info        ),
    .ir0_jalr_target_o   (ir0_jalr_target    ),
    .ir1_jalr_target_o   (ir1_jalr_target    ),
    .ir0_cjalr_err_o     (ir0_cjalr_err      ),
    .ir1_cjalr_err_o     (ir1_cjalr_err      )
  );

  alu_pipeline #(.CHERIoTEn(CHERIoTEn)) alu_pipeline0_i (
    .clk_i             (clk_i           ),
    .rst_ni            (rst_ni          ),
    .cheri_pmode_i     (cheri_pmode_i   ),
    .flush_i           (cmt_flush       ),
    .us_valid_i        (ex_valid[1]     ), 
    .alupl_rdy_o       (alupl0_rdy      ),
    .instr_i           (ira_dec         ),
    .full_data2_i      (ira_full_data2_fwd),
    .waw_act_i         (waw_act         ),
    .pcc_cap_i         (pcc_cap_r       ),
    .csr_mstatus_mie_i (csr_mstatus_mie),
    .fwd_act_o         (alupl0_fwd_act  ),
    .fwd_info_o        (alupl0_fwd_info ),
    .ds_rdy_i          (cmt_alupl0_rdy  ),
    .alupl_valid_o     (alupl0_valid    ),
    .alupl_output_o    (alupl0_output   )
  );

  alu_pipeline #(.CHERIoTEn(CHERIoTEn)) alu_pipeline1_i (
    .clk_i             (clk_i           ),
    .rst_ni            (rst_ni          ),
    .cheri_pmode_i     (cheri_pmode_i   ),
    .flush_i           (cmt_flush       ),
    .us_valid_i        (ex_valid[2]     ), 
    .alupl_rdy_o       (alupl1_rdy      ),
    .instr_i           (irb_dec         ),
    .full_data2_i      (irb_full_data2_fwd),
    .waw_act_i         (waw_act         ),
    .pcc_cap_i         (pcc_cap_r       ),
    .csr_mstatus_mie_i (csr_mstatus_mie ),
    .fwd_act_o         (alupl1_fwd_act  ),
    .fwd_info_o        (alupl1_fwd_info ),
    .ds_rdy_i          (cmt_alupl1_rdy  ),
    .alupl_valid_o     (alupl1_valid    ),
    .alupl_output_o    (alupl1_output   )
  );

  ls_pipeline # (.CHERIoTEn  (CHERIoTEn ), 
                 .EarlyLoad  (EarlyLoad ), 
                 .DCacheEn   (DCacheEn  ),
                 .LoadFiltEn (LoadFiltEn),
                 .HeapBase   (HeapBase  ),
                 .TSMapSize  (TSMapSize ) 

  ) ls_pipeline_i ( 
    .clk_i              (clk_i             ),
    .rst_ni             (rst_ni            ),
    .flush_i            (cmt_flush         ),
    .cheri_pmode_i      (cheri_pmode_i     ),
    .debug_mode_i       (1'b0              ),
    .us_valid_i         (ex_valid[3]       ),
    .lspl_rdy_o         (lspl_rdy          ),
    .sel_ira_i          (lspl_sel_ira      ),
    .ira_dec_i          (ira_dec           ),
    .irb_dec_i          (irb_dec           ),
    .ira_full_data2_i   (ira_full_data2_fwd),
    .irb_full_data2_i   (irb_full_data2_fwd),
    .ds_rdy_i           (cmt_lspl_rdy      ),
    .lspl_valid_o       (lspl_valid        ),
    .lspl_output_o      (lspl_output       ),
    .data_req_o         (data_req_o        ),
    .data_we_o          (data_we_o         ),
    .data_be_o          (data_be_o         ),
    .data_is_cap_o      (data_is_cap_o     ),
    .data_addr_o        (data_addr_o       ),
    .data_wdata_o       (data_wdata_o      ),
    .data_gnt_i         (data_gnt_i        ),
    .data_rvalid_i      (data_rvalid_i     ),
    .data_err_i         (data_err_i        ),
    .data_rdata_i       (data_rdata_i      ),
    .data_pmp_err_i     (1'b0              ),
    .waw_act_i          (waw_act           ),
    .fwd_act_o          (lspl_fwd_act      ),
    .fwd_info_o         (lspl_fwd_info     ),
    .trvk_en_o          (trvk_en           ), 
    .trvk_clrtag_o      (trvk_clrtag       ), 
    .trvk_addr_o        (trvk_addr         ),
    .trvk_outstanding_o (trvk_outstanding  ),
    .tsmap_cs_o         (tsmap_cs_o        ),
    .tsmap_addr_o       (tsmap_addr_o      ),
    .tsmap_rdata_i      (tsmap_rdata_i     ),   
    .csr_lsu_wr_req_o   (csr_lsu_wr_req    ),
    .csr_lsu_addr_o     (csr_lsu_addr      )
  );

  mult_pipeline # (
    .CHERIoTEn  (CHERIoTEn), 
    .NoMult     (NoMult), 
    .UseDWMult  (UseDWMult)
  ) mult_pipeline_i (
    .clk_i              (clk_i            ),
    .rst_ni             (rst_ni           ),
    .cheri_pmode_i      (cheri_pmode_i    ),
    .flush_i            (cmt_flush        ),
    .us_valid_i         (ex_valid[4]      ),
    .multpl_rdy_o       (multpl_rdy       ),
    .sel_ira_i          (multpl_sel_ira   ),
    .ira_dec_i          (ira_dec          ),
    .irb_dec_i          (irb_dec          ),
    .ira_full_data2_i   (ira_full_data2_fwd),
    .irb_full_data2_i   (irb_full_data2_fwd),
    .pcc_asr_i          (pcc_cap_r.perms[PERM_SR]),
    .waw_act_i          (waw_act          ),
    .fwd_act_o          (multpl_fwd_act   ),
    .fwd_info_o         (multpl_fwd_info  ),
    .ds_rdy_i           (cmt_multpl_rdy   ),
    .multpl_valid_o     (multpl_valid     ),
    .multpl_output_o    (multpl_output    ),
    .csr_access_o       (csr_access       ),
    .csr_cheri_o        (csr_cheri        ),
    .csr_op_en_o        (csr_op_en        ),
    .csr_op_o           (csr_op           ),
    .csr_addr_o         (csr_addr         ),
    .csr_wdata_o        (csr_wdata        ),
    .csr_rdata_i        (csr_rdata        ),
    .illegal_csr_insn_i (illegal_csr_insn ),
    .csr_mstatus_mie_i  (csr_mstatus_mie  ),
    .cheri_pcc_set_o    (cheri_pcc_set    ),
    .pcc_cap_i          (pcc_cap_r        ),
    .pcc_cap_o          (pcc_cap_w        ),
    .csr_set_mie_o      (csr_set_mie      ),
    .csr_clr_mie_o      (csr_clr_mie      )
  );
    

  committer # (.CHERIoTEn(CHERIoTEn)) committer_i (
    .clk_i              (clk_i              ),
    .rst_ni             (rst_ni             ),
    .cmt_flush_i        (cmt_flush          ),
    .sbdfifo_rd_valid_i (sbdfifo_rd_valid   ),
    .sbdfifo_rdata0_i   (sbdfifo_rdata0     ),
    .sbdfifo_rdata1_i   (sbdfifo_rdata1     ),
    .sbdfifo_rd_rdy_o   (sbdfifo_rd_rdy     ),
    .alupl0_valid_i     (alupl0_valid       ),
    .alupl0_output_i    (alupl0_output      ),
    .alupl0_rdy_o       (cmt_alupl0_rdy     ),
    .alupl1_valid_i     (alupl1_valid       ),
    .alupl1_output_i    (alupl1_output      ),
    .alupl1_rdy_o       (cmt_alupl1_rdy     ),
    .lspl_valid_i       (lspl_valid         ),
    .lspl_output_i      (lspl_output        ),
    .lspl_rdy_o         (cmt_lspl_rdy       ),
    .multpl_valid_i     (multpl_valid       ),
    .multpl_output_i    (multpl_output      ),
    .multpl_rdy_o       (cmt_multpl_rdy     ),
    .cmt_regwr_o        (cmt_regwr          ),
    .cmt_err_o          (cmt_err            ),
    .cmt_err_info_o     (cmt_err_info       ),
    .rf_waddr0_o        (rf_waddr0          ),
    .rf_wdata0_o        (rf_wdata0          ),
    .rf_we0_o           (rf_we0             ),
    .rf_waddr1_o        (rf_waddr1          ),
    .rf_wdata1_o        (rf_wdata1          ),
    .rf_we1_o           (rf_we1             ),
    .rf_waddr2_o        (rf_waddr2          ),
    .rf_wdata2_o        (rf_wdata2          ),
    .rf_we2_o           (rf_we2             )
  );                    
    
  cs_registers #(.CHERIoTEn (CHERIoTEn)) cs_registers_i (
    .clk_i                        (clk_i),
    .rst_ni                       (rst_ni),
    .cheri_pmode_i                (cheri_pmode_i),
    .hart_id_i                    (hart_id_i),

    .priv_mode_id_o               (),
    .priv_mode_lsu_o              (),
    .csr_mtvec_o                  (csr_mtvec),
    .csr_mtvec_init_i             (csr_mtvec_init),
    .boot_addr_i                  (boot_addr_i),
    .csr_access_i                 (csr_access),
    .csr_cheri_i                  (csr_cheri),
    .csr_op_en_i                  (csr_op_en),
    .csr_op_i                     (csr_op),
    .csr_addr_i                   (csr_addr),
    .csr_wdata_i                  (csr_wdata),
    .csr_rdata_o                  (csr_rdata),
    .illegal_csr_insn_o           (illegal_csr_insn),
                                  
    .csr_set_mie_i                (csr_set_mie),
    .csr_clr_mie_i                (csr_clr_mie),
    .csr_lsu_wr_req_i             (csr_lsu_wr_req),
    .csr_lsu_addr_i               (csr_lsu_addr),
                                  
    .irq_software_i               (irq_software_i),
    .irq_timer_i                  (irq_timer_i),
    .irq_external_i               (irq_external_i),
    .irq_fast_i                   (irq_fast_i),
    .irq_pending_o                (irq_pending),
    .irqs_o                       (irqs),
    .csr_mstatus_mie_o            (csr_mstatus_mie),
    .csr_mstatus_tw_o             (csr_mstatus_tw),
    .csr_mepc_o                   (csr_mepc),
                                  
    .csr_pmp_cfg_o                (),
    .csr_pmp_addr_o               (),
    .csr_pmp_mseccfg_o            (),

    .csr_depc_o                   (),
    .debug_mode_i                 (1'b0),
    .debug_mode_entering_i        (1'b0),
    .debug_cause_i                (DBG_CAUSE_NONE),
    .debug_pc_i                   (32'h0),
    .debug_csr_save_i             (1'b0),
    .debug_single_step_o          (),
    .debug_ebreakm_o              (),
    .debug_ebreaku_o              (),
    .trigger_match_o              (),

    .data_ind_timing_o            (),
    .dummy_instr_en_o             (),
    .dummy_instr_mask_o           (),
    .dummy_instr_seed_en_o        (),
    .dummy_instr_seed_o           (),
    .icache_enable_o              (),
    .csr_shadow_err_o             (),

    .csr_exc_pc_i                 (csr_exc_pc),
    .csr_save_cause_i             (csr_save_cause),
    .csr_restore_mret_i           (csr_restore_mret),
    .csr_restore_dret_i           (csr_restore_dret),
    .csr_mepcc_clrtag_i           (csr_mepcc_clrtag),
    .csr_mcause_i                 (csr_exc_cause),
    .csr_mtval_i                  (csr_mtval),

    .double_fault_seen_o          (),

    .instr_ret_i                  (1'b0),
    .instr_ret_compressed_i       (1'b0),
    .instr_ret_spec_i             (1'b0),
    .instr_ret_compressed_spec_i  (1'b0),
    .iside_wait_i                 (1'b0),
    .jump_i                       (1'b0),
    .branch_i                     (1'b0),
    .branch_taken_i               (1'b0),
    .mem_load_i                   (1'b0),
    .mem_store_i                  (1'b0),
    .dside_wait_i                 (1'b0),
    .mul_wait_i                   (1'b0),
    .div_wait_i                   (1'b0),

    .cheri_pcc_set_i              (cheri_pcc_set),
    .pcc_cap_i                    (pcc_cap_w),
    .pcc_cap_o                    (pcc_cap_r),
    .csr_dbg_tclr_fault_o         (),
    .cheri_fatal_err_o            ()
  );

`ifdef  RVFI
  tracer_wrapper  tracer_wrapper_i (
    .clk_i         (clk_i         ),
    .rst_ni        (rst_ni        ),
    .cheri_pmode_i (cheri_pmode_i )
  );
`endif

endmodule
