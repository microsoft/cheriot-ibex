// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Load/Store pipeline 
//

module ls_pipeline import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; # (
  parameter bit          CHERIoTEn  = 1'b1,
  parameter bit          LoadFiltEn = 1'b1,
  parameter bit          EarlyLoad  = 1'b1,
  parameter bit          DCacheEn   = 1'b1,
  parameter int unsigned HeapBase  = 32'h2001_0000,
  parameter int unsigned TSMapSize = 1024
) (
  input  logic            clk_i,
  input  logic            rst_ni,

  input  logic            cheri_pmode_i,
  input  logic            debug_mode_i,

  // upstream (issuer) side interface
  input  logic            flush_i,
  input  logic            us_valid_i,
  output logic            lspl_rdy_o,
  input  logic            sel_ira_i,
  input  ir_dec_t         ira_dec_i,
  input  ir_dec_t         irb_dec_i,
  input  full_data2_t     ira_full_data2_i,
  input  full_data2_t     irb_full_data2_i,

  // downstream (commit) side interface
  input  logic            ds_rdy_i,
  output logic            lspl_valid_o,
  output pl_out_t         lspl_output_o,

  // data memory interface
  output logic            data_req_o,
  output logic            data_we_o,
  output logic [3:0]      data_be_o,
  output logic            data_is_cap_o,
  output logic [31:0]     data_addr_o,
  output logic [MemW-1:0] data_wdata_o,
  input  logic            data_gnt_i,
  input  logic            data_rvalid_i,
  input  logic            data_err_i,
  input  logic [MemW-1:0] data_rdata_i,
  input  logic            data_pmp_err_i,

  // data fwd interface
  input  waw_act_t        waw_act_i,
  output logic [31:0]     fwd_act_o,
  output pl_fwd_t         fwd_info_o,

  // trvk and tsmap interface
  output logic [4:0]      trvk_addr_o,
  output logic            trvk_en_o,
  output logic            trvk_clrtag_o,
  output logic            trvk_outstanding_o,
                          
  output logic            tsmap_cs_o,
  output logic [15:0]     tsmap_addr_o,
  input  logic [31:0]     tsmap_rdata_i,
  output logic            csr_lsu_wr_req_o,
  output logic [31:0]     csr_lsu_addr_o
);

  localparam WbFifoW = $bits(pl_out_t);

  ir_dec_t         instr_dec;
  full_data2_t     full_data2;
  full_cap_t       cs1_fcap, cs2_fcap;

  lsu_req_info_t   lsu_req_dec, lsu_req_info;

  logic               lsu_req;      
  logic               lsu_req_done;      
  logic               lsu_resp_valid;
  pl_out_t            lsu_resp_info;
  logic               lsu_resp_err;
  logic               wb_rdy, wb_fifo_rdy;
  logic [WbFifoW-1:0] wb_fifo_rdata;
  logic               waw_fifo_wvalid;
  logic [5:0]         waw_fifo_wdata, waw_fifo_rdata;
                   
  logic            data_pmp_err;
                   
  logic [11:0]     ira_imm12, irb_imm12;
  logic [31:0]     ira_ls_addr, irb_ls_addr;
 
  opcode_e         opcode;
  logic [1:0]      data_type;
                   
  logic            lspl_valid;
  logic            lsu_err_active, resp_err_latched;
  logic            cheri_pmode;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  //
  //  EX1 (address generation) stage
  // 
  
  // select input
  assign instr_dec  = sel_ira_i ? ira_dec_i : irb_dec_i;
  assign full_data2 = sel_ira_i ? ira_full_data2_i : irb_full_data2_i;
 
  assign ira_imm12 = ira_dec_i.rf_we ? ira_dec_i.insn[31:20] : {ira_dec_i.insn[31:25], ira_dec_i.insn[11:7]};
  assign irb_imm12 = irb_dec_i.rf_we ? irb_dec_i.insn[31:20] : {irb_dec_i.insn[31:25], irb_dec_i.insn[11:7]};

  assign ira_ls_addr = ira_full_data2_i.d0[31:0] + {{20{ira_imm12[11]}}, ira_imm12};
  assign irb_ls_addr = irb_full_data2_i.d0[31:0] + {{20{irb_imm12[11]}}, irb_imm12};

  assign cs1_fcap       = full_cap_t'(full_data2.d0);
  assign cs2_fcap       = full_cap_t'(full_data2.d1);

  // decode and address generation
  assign opcode   = opcode_e'(instr_dec.insn[6:0]);

  always_comb begin
    logic          lc_cglg, lc_csdlm, lc_ctag;
    logic          is_cap;

    unique case (instr_dec.insn[13:12])
      2'b00:   data_type = 2'b10; // sb
      2'b01:   data_type = 2'b01; // sh
      2'b10:   data_type = 2'b00; // sw
      default: data_type = 2'b00;
    endcase

    lc_cglg   = ~cs1_fcap.perms[PERM_LG];
    lc_csdlm  = ~cs1_fcap.perms[PERM_LM];
    lc_ctag   = ~cs1_fcap.perms[PERM_MC];
    
    is_cap    = instr_dec.cheri_op.clc | instr_dec.cheri_op.csc;

    lsu_req_dec = NULL_LSU_REQ_INFO;

    lsu_req_dec            = NULL_LSU_REQ_INFO;
    lsu_req_dec.rf_we      = (opcode == OPCODE_LOAD);
    lsu_req_dec.is_cap     = is_cap;
    lsu_req_dec.data_type  = data_type;
    lsu_req_dec.wdata      = (cheri_pmode & is_cap) ? op2memcap(full_data2.d1[OpW-1:0]) : 
                                                      full_data2.d1[MemW-1:0];   
    lsu_req_dec.clrperm    = debug_mode_i ? 4'h0 : {lc_ctag, 1'b0, lc_csdlm, lc_cglg};
    lsu_req_dec.sign_ext   = ~instr_dec.insn[14]; 
    lsu_req_dec.addr       = sel_ira_i ? ira_ls_addr : irb_ls_addr;
    lsu_req_dec.pc         = instr_dec.pc;
    lsu_req_dec.rs1        = instr_dec.rs1;
    lsu_req_dec.rd         = instr_dec.rd;

    if (cheri_pmode) lsu_req_dec.lschk_info =  build_lschk_info(cs1_fcap, cs2_fcap);
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      resp_err_latched  <= 1'b0;
    end else begin
      if (flush_i)
        resp_err_latched  <= 1'b0;
      else if (lsu_resp_err)
        resp_err_latched  <= 1'b1;
    end
  end
  
  assign lsu_err_active = resp_err_latched | lsu_resp_err;

  assign wb_rdy = wb_fifo_rdy & ~lsu_err_active;

  // Output to commit 
  always_comb begin
    lspl_valid_o       = lspl_valid;
    lspl_output_o      = pl_out_t'(wb_fifo_rdata);
    lspl_output_o.wrsv = lspl_output_o.we & waw_fifo_rdata[5];
  end

  // Output to CSR (for mshwm update)
  //  note for mshmwm we only care about write accesses, no need to include resp-side checks
  assign csr_lsu_wr_req_o = lsu_req & lsu_req_done & ~lsu_req_info.rf_we & ~lsu_req_info.cheri_err;
  assign csr_lsu_addr_o   = lsu_req_info.addr;

  //
  // LSU interface
  // 
  lsu_if # (.CHERIoTEn(CHERIoTEn), .EarlyLoad(EarlyLoad)) lsu_if_i (
    .clk_i             (clk_i         ),
    .rst_ni            (rst_ni        ),
    .cheri_pmode_i     (cheri_pmode_i ),
    .flush_i           (flush_i       ),
    .us_valid_i        (us_valid_i    ),
    .lsu_req_dec_i     (lsu_req_dec   ),
    .lsif_rdy_o        (lspl_rdy_o    ),
    .lsu_req_done_i    (lsu_req_done  ),
    .lsu_req_o         (lsu_req       ),
    .lsu_req_info_o    (lsu_req_info  )
    );

  //
  // LSU
  // 
  assign data_pmp_err = 1'b0;

  load_store_unit #(.CHERIoTEn(CHERIoTEn)) load_store_unit_i (
    .clk_i                 (clk_i             ),
    .rst_ni                (rst_ni            ),
    .cheri_pmode_i         (cheri_pmode_i     ),
    .data_req_o            (data_req_o        ),
    .data_is_cap_o         (data_is_cap_o     ),
    .data_gnt_i            (data_gnt_i        ),
    .data_rvalid_i         (data_rvalid_i     ),
    .data_err_i            (data_err_i        ),
    .data_pmp_err_i        (data_pmp_err      ),
    .data_addr_o           (data_addr_o       ),
    .data_we_o             (data_we_o         ),
    .data_be_o             (data_be_o         ),
    .data_wdata_o          (data_wdata_o      ),
    .data_rdata_i          (data_rdata_i      ),
    .lsu_req_i             (lsu_req           ),      
    .lsu_req_done_o        (lsu_req_done      ),
    .lsu_req_info_i        (lsu_req_info      ),
    .addr_last_o           (),
    .ds_rdy_i              (wb_rdy            ),      
    .lsu_resp_valid_o      (lsu_resp_valid    ),
    .lsu_resp_err_o        (lsu_resp_err      ),
    .lsu_resp_info_o       (lsu_resp_info     ),
    .busy_o                (),
    .perf_load_o           (),
    .perf_store_o          ()
  );

  // 
  // WB stage (output fifo)
  //
  wt_fifo # (.Depth(2), .Width(WbFifoW)) wb_fifo_i (
    .clk_i       (clk_i         ),
    .rst_ni      (rst_ni        ),
    .flush_i     (flush_i       ),     // QQQ do we actually need this??
    .wr_valid_i  (lsu_resp_valid),
    .wr_data_i   (lsu_resp_info ),
    .wr_rdy_o    (wb_fifo_rdy   ), 
    .rd_rdy_i    (ds_rdy_i      ),
    .rd_valid_o  (lspl_valid    ),
    .rd_data_o   (wb_fifo_rdata ),
    .waw_req_i   (2'b00         ),
    .waw_addr0_i (5'h0          ),
    .waw_addr1_i (5'h0          )
    );

  //
  // WAW status tracking FIFO 
  //
  // QQQ this FIFO should never overflow/underflow. assertions?

  assign waw_fifo_wvalid = us_valid_i & lspl_rdy_o;
  assign waw_fifo_wdata  = {1'b1, instr_dec.rd};

  wt_fifo # (.Depth(8), .Width(6), .WaWTracking(1'b1)) waw_fifo_i (
    .clk_i       (clk_i          ),
    .rst_ni      (rst_ni         ),
    .flush_i     (flush_i        ),
    .wr_valid_i  (waw_fifo_wvalid),
    .wr_data_i   (waw_fifo_wdata ),
    .wr_rdy_o    (), 
    .rd_rdy_i    (ds_rdy_i       ),
    .rd_valid_o  (),
    .rd_data_o   (waw_fifo_rdata ),
    .waw_req_i   (waw_act_i.valid),
    .waw_addr0_i (waw_act_i.rd0  ),
    .waw_addr1_i (waw_act_i.rd1  )
    );

  //
  // WAW status tracking FIFO 

  //
  // Data Cache
  // 
  
  // QQQ, keep this for now till we can modify dcache
  logic load_err, store_err;

  assign load_err  = lsu_resp_err & lsu_resp_info.we;
  assign store_err = lsu_resp_err & ~lsu_resp_info.we;

  if (DCacheEn) begin
    dcache dcache_i (
      .clk_i            (clk_i           ),            
      .rst_ni           (rst_ni          ),
      .instr_i          (instr_dec       ),
      .lsu_req_i        (lsu_req         ),
      .lsu_req_info_i   (lsu_req_info    ),
      .lsu_rdy_i        (lsu_req_done    ),
      .lsu_resp_valid_i (lsu_resp_valid  ),
      .load_err_i       (load_err        ),
      .store_err_i      (store_err       ),
      .data_rdata_i     (data_rdata_i    ),
      .waw_act_i        (waw_act_i       ),
      .fwd_act_o        (fwd_act_o       ),
      .fwd_info_o       (fwd_info_o      )    
    );
  end else begin
    assign fwd_act_o   = 32'h0;
    assign fwd_info_o = NULL_PL_FWD;
  end

  if (CHERIoTEn & LoadFiltEn) begin : gen_trvk
    logic         clc_valid, clc_err;
    logic [4:0]   clc_rd;
    reg_cap_t     clc_rcap;

    assign clc_valid = lspl_valid_o & ds_rdy_i & lspl_output_o.is_cap & lspl_output_o.we;
    assign clc_err   = lspl_output_o.err;
    assign clc_rd    = lspl_output_o.waddr;
    assign clc_rcap  = reg_cap_t'(lspl_output_o.wdata);

    cheri_trvk_stage #(
      .HeapBase  (HeapBase),
      .TSMapSize (TSMapSize)
    ) cheri_trvk_stage_i (
      .clk_i              (clk_i             ),
      .rst_ni             (rst_ni            ),
      .clc_valid_i        (clc_valid         ),
      .clc_rd_i           (clc_rd            ),
      .clc_err_i          (clc_err           ),
      .clc_rcap_i         (clc_rcap          ),
      .trvk_addr_o        (trvk_addr_o       ),
      .trvk_en_o          (trvk_en_o         ),
      .trvk_clrtag_o      (trvk_clrtag_o     ),
      .trvk_outstanding_o (trvk_outstanding_o),
      .tsmap_cs_o         (tsmap_cs_o        ),
      .tsmap_addr_o       (tsmap_addr_o      ),
      .tsmap_rdata_i      (tsmap_rdata_i     )
    );

  end else begin : gen_no_trvk
    assign trvk_addr_o        = 5'h0;
    assign trvk_en_o          = 1'b0;
    assign trvk_clrtag_o      = 1'b0;
    assign trvk_outstanding_o = 1'b0;

    assign tsmap_cs_o   = 1'b0;
    assign tsmap_addr_o = 16'h0;
 end

 // RVFI tracking of mem_addr and mem_wdata
`ifndef SYNTHESIS
   logic [31:0]      rvfi_mem_addr;
   logic [MemW-1:0]  rvfi_mem_wdata;
   logic [MemW+31:0] rvfi_fifo_rdata;

   wt_fifo # (.Depth(8), .Width(MemW+32)) rvfi_fifo_i (
    .clk_i       (clk_i          ),
    .rst_ni      (rst_ni         ),
    .flush_i     (flush_i        ),
    .wr_valid_i  ((lsu_req & lsu_req_done)),
    .wr_data_i   ({lsu_req_info.wdata, lsu_req_info.addr}),
    .wr_rdy_o    (), 
    .rd_rdy_i    (ds_rdy_i       ),
    .rd_valid_o  (),
    .rd_data_o   (rvfi_fifo_rdata ),
    .waw_req_i   (2'b00         ),
    .waw_addr0_i (5'h0          ),
    .waw_addr1_i (5'h0          )
    );

   assign rvfi_mem_addr  = rvfi_fifo_rdata[31:0];
   assign rvfi_mem_wdata = rvfi_fifo_rdata[MemW+31: 32];

`endif

endmodule
