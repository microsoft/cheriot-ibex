// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Instruction registers and decoder
//
module ir_stage import super_pkg::*; import cheri_pkg::*; #(
  parameter bit          TwoStage   = 1'b0,
  parameter bit          CHERIoTEn  = 1'b0,
  parameter rv32m_e      RV32M      = super_pkg::RV32MFast,
  parameter rv32b_e      RV32B      = super_pkg::RV32BNone
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic             cheri_pmode_i,
  input  logic             debug_mode_i,

  // CSR interface
  input  pcc_cap_t         pcc_cap_i,

  // IF interface
  input  ir_reg_t          us_instr0_i,       
  input  ir_reg_t          us_instr1_i,      
  input  logic [1:0]       us_valid_i,
  output logic [1:0]       ir_rdy_o,

  // regfile interface
  input  rf_rdata2_t       rf_rdata2_p0_i,
  input  rf_rdata2_t       rf_rdata2_p1_i,
  output rf_raddr2_t       rf_raddr2_p0_o,
  output rf_raddr2_t       rf_raddr2_p1_o,

  input  logic [4:0]       rf_waddr0_i,
  input  logic [RegW-1:0]  rf_wdata0_i,
  input  logic             rf_we0_i,     
  input  logic [4:0]       rf_waddr1_i,
  input  logic [RegW-1:0]  rf_wdata1_i,
  input  logic             rf_we1_i,    
  input  logic [4:0]       rf_waddr2_i,
  input  logic [RegW-1:0]  rf_wdata2_i,
  input  logic             rf_we2_i,    

  // Issuer interface
  input  logic             ir_flush_i,
  input  logic  [1:0]      ds_rdy_i,
  output logic [1:0]       ir_valid_o,
  output logic             ira_is0_o,
  output ir_dec_t          ira_dec_o,
  output ir_dec_t          irb_dec_o,
  output op_data2_t        ira_op_rf_rdata2_o,       // cheri-expanded register
  output op_data2_t        irb_op_rf_rdata2_o,

  // Revocation tag clearing interface
  input  logic             trvk_en_i,
  input  logic             trvk_clrtag_i,
  input  logic [4:0]       trvk_addr_i
);

  localparam irRegW = $bits(ir_reg_t);
  localparam irDecW = $bits(ir_dec_t);

  //
  // Update function for registers value read from RF directly (used in 1-stage case)
  // used only for trvk tag-clearing
  //
  function automatic rf_rdata2_t update_rdata_1stage (
    logic             cheri_pmode,
    rf_rdata2_t       rf_rdata2,
    rf_raddr2_t       rf_raddr2,
    logic             trvk_en_i,
    logic             trvk_clrtag_i,
    logic [4:0]       trvk_addr_i
  );
    rf_rdata2_t       result;
    logic             clrtag0, clrtag1;
    logic [RegW-1:0]  clrtag_mask0, clrtag_mask1;

    clrtag0       = cheri_pmode & trvk_en_i & trvk_clrtag_i && (trvk_addr_i == rf_raddr2.a0);
    clrtag_mask0  = {~clrtag0, {REG_TAG{1'b1}}};
    clrtag1       = cheri_pmode & trvk_en_i & trvk_clrtag_i && (trvk_addr_i == rf_raddr2.a1);
    clrtag_mask1  = {~clrtag1, {REG_TAG{1'b1}}};

    result.d0 = result.d0 & clrtag_mask0;
    result.d1 = result.d0 & clrtag_mask1;

    return result;

  endfunction

  //
  // Update function for pre-loaded registers (used in 2-stage case)
  //
  function automatic rf_rdata2_t update_rdata_2stage (
    logic             cheri_pmode,
    rf_rdata2_t       cur_val,
    logic [1:0]       wr_mem, 
    rf_raddr2_t       raddr2,
    rf_raddr2_t       raddr2_q,
    rf_rdata2_t       rf_rdata2_p0_i,
    rf_rdata2_t       rf_rdata2_p1_i,
    logic [4:0]       rf_waddr0_i,
    logic [RegW-1:0]  rf_wdata0_i,
    logic             rf_we0_i,     
    logic [4:0]       rf_waddr1_i,
    logic [RegW-1:0]  rf_wdata1_i,
    logic             rf_we1_i,    
    logic [4:0]       rf_waddr2_i,
    logic [RegW-1:0]  rf_wdata2_i,
    logic             rf_we2_i,
    logic             trvk_en_i,
    logic             trvk_clrtag_i,
    logic [4:0]       trvk_addr_i
    );    
  
    rf_rdata2_t      result;  
    logic            rf_load;
    logic            clrtag0, clrtag1;
    logic [RegW-1:0] clrtag_mask0, clrtag_mask1;

    rf_load = wr_mem[0] | wr_mem[1];

    clrtag0      = cheri_pmode & trvk_en_i & trvk_clrtag_i & 
                   ((rf_load & (trvk_addr_i == raddr2.a0)) | 
                    (~rf_load & (trvk_addr_i == raddr2_q.a0)));
    clrtag1      = cheri_pmode & trvk_en_i & trvk_clrtag_i & 
                   ((rf_load & (trvk_addr_i == raddr2.a1)) | 
                    (~rf_load & (trvk_addr_i == raddr2_q.a1)));

    clrtag_mask0 = {~clrtag0, {REG_TAG{1'b1}}};
    clrtag_mask1 = {~clrtag1, {REG_TAG{1'b1}}};

    result = cur_val;

    // initial write and regfile bypass
    //  - note, we choose not to mux a0 and a1 here to enablle pre-calcuation for timing
    if ((rf_load & rf_we2_i && (raddr2.a0 == rf_waddr2_i)) ||
        (~rf_load & rf_we2_i && (raddr2_q.a0 == rf_waddr2_i)))
      result.d0 = rf_wdata2_i;
    else if ((rf_load & rf_we1_i && (raddr2.a0 == rf_waddr1_i)) ||
             (~rf_load & rf_we1_i && (raddr2_q.a0 == rf_waddr1_i)))
      result.d0 = rf_wdata1_i;
    else if ((rf_load & rf_we0_i && (raddr2.a0 == rf_waddr0_i)) ||
             (~rf_load & rf_we0_i && (raddr2_q.a0 == rf_waddr0_i)))
      result.d0 = rf_wdata0_i;
    else if (wr_mem[0])
      result.d0 = rf_rdata2_p0_i.d0;
    else if (wr_mem[1])
      result.d0 = rf_rdata2_p1_i.d0;

    result.d0 = result.d0 & clrtag_mask0;

    if ((rf_load & rf_we2_i && (raddr2.a1 == rf_waddr2_i)) ||
        (~rf_load & rf_we2_i && (raddr2_q.a1 == rf_waddr2_i)))
      result.d1 = rf_wdata2_i;
    else if ((rf_load & rf_we1_i && (raddr2.a1 == rf_waddr1_i)) ||
             (~rf_load & rf_we1_i && (raddr2_q.a1 == rf_waddr1_i)))
      result.d1 = rf_wdata1_i;
    else if ((rf_load & rf_we0_i && (raddr2.a1 == rf_waddr0_i)) ||
             (~rf_load & rf_we0_i && (raddr2_q.a1 == rf_waddr0_i)))
      result.d1 = rf_wdata0_i;
    else if (wr_mem[0])
      result.d1 = rf_rdata2_p0_i.d1;
    else if (wr_mem[1])
      result.d1 = rf_rdata2_p1_i.d1;

    result.d1 = result.d1 & clrtag_mask1;

    return result;
  endfunction

  logic fifo_mema_is0;
  logic cheri_pmode;

  ir_reg_t ira_reg, irb_reg;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  if (TwoStage) begin : gen_ir_2stage
    logic [1:0]  s0_rd_rdy, s0_rd_valid;
    logic [1:0]  s1_wr_valid, s1_wr_rdy;
    logic [1:0]  s1_wr_mema, s1_wr_memb;
    logic        s1_wr_ptr;

    ir_reg_t     s0_reg0, s0_reg1;
    ir_reg_t     s0_cdec_reg0, s0_cdec_reg1;
    ir_dec_t     s1_dec0, s1_dec1;

    rf_rdata2_t  ira_rf_rdata2_d, irb_rf_rdata2_d;
    rf_rdata2_t  ira_rf_rdata2_q, irb_rf_rdata2_q;
    rf_raddr2_t  ira_raddr2, irb_raddr2;
    rf_raddr2_t  ira_raddr2_q, irb_raddr2_q;

    stage_fifo # (.Width(irRegW), .PeekMem(0)) s0_fifo (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .flush_i    (ir_flush_i),
      .wr_valid_i (us_valid_i),
      .wr_data0_i (us_instr0_i),  
      .wr_data1_i (us_instr1_i), 
      .wr_rdy_o   (ir_rdy_o), 
      .rd_rdy_i   (s0_rd_rdy),
      .rd_valid_o (s0_rd_valid),
      .rd_data0_o (s0_reg0),
      .rd_data1_o (s0_reg1),
      .mema_is0_o (),
      .wr_mema_o  (),
      .wr_memb_o  (),
      .wr_ptr_o   (),
      .mema_o     (),
      .memb_o     ()
    );

    compressed_decoder #(
      .CHERIoTEn (CHERIoTEn)
    ) compressed_decoder_0 (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .cheri_pmode_i  (cheri_pmode_i),
      .instr_i        (s0_reg0),
      .instr_o        (s0_cdec_reg0)
    );

    compressed_decoder #(
      .CHERIoTEn (CHERIoTEn)
    ) compressed_decoder_1 (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .cheri_pmode_i  (cheri_pmode_i),
      .instr_i        (s0_reg1),
      .instr_o        (s0_cdec_reg1)
    );

    ir_decoder #(
      .CHERIoTEn (CHERIoTEn),
      .RV32M     (RV32M),   
      .RV32B     (RV32B)  
    ) ir0_decoder_i (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .cheri_pmode_i (cheri_pmode_i),
      .debug_mode_i  (debug_mode_i),
      .pcc_cap_i     (pcc_cap_i),
      .ir_reg_i      (s0_cdec_reg0),
      .ir_dec_o      (s1_dec0)
    );

    ir_decoder #(
      .CHERIoTEn (CHERIoTEn),
      .RV32M     (RV32M),   
      .RV32B     (RV32B)  
    ) ir1_decoder_i (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .cheri_pmode_i (cheri_pmode_i),
      .debug_mode_i  (debug_mode_i),
      .pcc_cap_i     (pcc_cap_i),
      .ir_reg_i      (s0_cdec_reg1),
      .ir_dec_o      (s1_dec1)
    );
 
    // cascade wr/rd signals between 2 fifo stages 
    assign s1_wr_valid = s0_rd_valid;
    assign s0_rd_rdy   = s1_wr_rdy;

    stage_fifo # (.Width(irDecW), .PeekMem(1)) s1_fifo (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .flush_i    (ir_flush_i),
      .wr_valid_i (s1_wr_valid),
      .wr_data0_i (s1_dec0),  
      .wr_data1_i (s1_dec1), 
      .wr_rdy_o   (s1_wr_rdy), 
      .rd_rdy_i   (ds_rdy_i),
      .rd_valid_o (ir_valid_o),
      .rd_data0_o (),
      .rd_data1_o (),
      .mema_is0_o (ira_is0_o),
      .wr_mema_o  (s1_wr_mema),
      .wr_memb_o  (s1_wr_memb),
      .wr_ptr_o   (s1_wr_ptr),
      .mema_o     (ira_dec_o),
      .memb_o     (irb_dec_o)
    );

    assign rf_raddr2_p0_o.a0 = s1_dec0.rs1;
    assign rf_raddr2_p0_o.a1 = s1_dec0.rs2;
    assign rf_raddr2_p1_o.a0 = s1_dec1.rs1;
    assign rf_raddr2_p1_o.a1 = s1_dec1.rs2;

    ir_dec_t ira_dec_in, irb_dec_in;

    // use s1_wr_ptr instead s1_wr_mem to help timing (s1_wr_mem include ds_rdy)
    assign ira_dec_in = ~s1_wr_ptr ? s1_dec0 : s1_dec1; 
    assign irb_dec_in =  s1_wr_ptr ? s1_dec0 : s1_dec1; 

    assign ira_raddr2.a0 = ira_dec_in.rs1;
    assign ira_raddr2.a1 = ira_dec_in.rs2;
    assign irb_raddr2.a0 = irb_dec_in.rs1;
    assign irb_raddr2.a1 = irb_dec_in.rs2;
    
    assign ira_rf_rdata2_d = update_rdata_2stage (
          .cheri_pmode     (cheri_pmode    ),
          .cur_val         (ira_rf_rdata2_q),
          .wr_mem          (s1_wr_mema     ),
          .raddr2          (ira_raddr2     ),
          .raddr2_q        (ira_raddr2_q   ),
          .rf_rdata2_p0_i  (rf_rdata2_p0_i ),
          .rf_rdata2_p1_i  (rf_rdata2_p1_i ),
          .rf_waddr0_i     (rf_waddr0_i    ),
          .rf_wdata0_i     (rf_wdata0_i    ),
          .rf_we0_i        (rf_we0_i       ),
          .rf_waddr1_i     (rf_waddr1_i    ),
          .rf_wdata1_i     (rf_wdata1_i    ),
          .rf_we1_i        (rf_we1_i       ),
          .rf_waddr2_i     (rf_waddr2_i    ),
          .rf_wdata2_i     (rf_wdata2_i    ),
          .rf_we2_i        (rf_we2_i       ),
          .trvk_en_i       (trvk_en_i      ),
          .trvk_clrtag_i   (trvk_clrtag_i  ), 
          .trvk_addr_i     (trvk_addr_i    ) 
          ); 
    
    assign irb_rf_rdata2_d = update_rdata_2stage (
          .cheri_pmode     (cheri_pmode    ),
          .cur_val         (irb_rf_rdata2_q),
          .wr_mem          (s1_wr_memb     ),
          .raddr2          (irb_raddr2     ),
          .raddr2_q        (irb_raddr2_q   ),
          .rf_rdata2_p0_i  (rf_rdata2_p0_i ),
          .rf_rdata2_p1_i  (rf_rdata2_p1_i ),
          .rf_waddr0_i     (rf_waddr0_i    ),
          .rf_wdata0_i     (rf_wdata0_i    ),
          .rf_we0_i        (rf_we0_i       ),
          .rf_waddr1_i     (rf_waddr1_i    ),
          .rf_wdata1_i     (rf_wdata1_i    ),
          .rf_we1_i        (rf_we1_i       ),
          .rf_waddr2_i     (rf_waddr2_i    ),
          .rf_wdata2_i     (rf_wdata2_i    ),
          .rf_we2_i        (rf_we2_i       ),
          .trvk_en_i       (trvk_en_i      ),
          .trvk_clrtag_i   (trvk_clrtag_i  ), 
          .trvk_addr_i     (trvk_addr_i    ) 
          ); 
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        ira_rf_rdata2_q <= '{0, 0};
        irb_rf_rdata2_q <= '{0, 0};
        ira_raddr2_q    <= '{0, 0}; 
        irb_raddr2_q    <= '{0, 0};
      end else begin
        ira_rf_rdata2_q <= ira_rf_rdata2_d;
        irb_rf_rdata2_q <= irb_rf_rdata2_d;

        // split raddr_q from ira_dec_o.rs1/rs2 to reduce fanout
        if (|s1_wr_mema) ira_raddr2_q <= ira_raddr2; 

        if (|s1_wr_memb) irb_raddr2_q <= irb_raddr2; 
      end
    end

    // QQQ cheri expansion
    if (CHERIoTEn) begin
  
      assign ira_op_rf_rdata2_o.d0 = reg2opcap(ira_rf_rdata2_q.d0);
      assign ira_op_rf_rdata2_o.d1 = reg2opcap(ira_rf_rdata2_q.d1); 
      assign irb_op_rf_rdata2_o.d0 = reg2opcap(irb_rf_rdata2_q.d0);
      assign irb_op_rf_rdata2_o.d1 = reg2opcap(irb_rf_rdata2_q.d1);
    end else begin
      assign ira_op_rf_rdata2_o.d0 = ira_rf_rdata2_q.d0;
      assign ira_op_rf_rdata2_o.d1 = ira_rf_rdata2_q.d1;
      assign irb_op_rf_rdata2_o.d0 = irb_rf_rdata2_q.d0;
      assign irb_op_rf_rdata2_o.d1 = irb_rf_rdata2_q.d1;
    end

  end else begin : gen_ir_1stage

    stage_fifo # (.Width(irRegW), .PeekMem(1)) ir_fifo (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .flush_i    (ir_flush_i),
      .wr_valid_i (us_valid_i),
      .wr_data0_i (us_instr0_i),  
      .wr_data1_i (us_instr1_i), 
      .wr_rdy_o   (ir_rdy_o), 
      .rd_rdy_i   (ds_rdy_i),
      .rd_valid_o (ir_valid_o),
      .rd_data0_o (),
      .rd_data1_o (),
      .mema_is0_o (ira_is0_o),
      .wr_mema_o  (),
      .wr_memb_o  (),
      .mema_o     (ira_reg),
      .memb_o     (irb_reg)
    );

    ir_decoder #(
      .CHERIoTEn (CHERIoTEn),
      .RV32M     (RV32M),   
      .RV32B     (RV32B)  
    ) ir0_decoder_i (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .ir_reg_i   (ira_reg),
      .ir_dec_o   (ira_dec_o)
    );

    ir_decoder #(
      .CHERIoTEn (CHERIoTEn),
      .RV32M     (RV32M),   
      .RV32B     (RV32B)  
    ) ir1_decoder_i (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
    .ir_reg_i   (irb_reg),
    .ir_dec_o   (irb_dec_o)
    );

    assign rf_raddr2_p0_o.a0 = ira_dec_o.rs1;
    assign rf_raddr2_p0_o.a1 = ira_dec_o.rs2;
    assign rf_raddr2_p1_o.a0 = irb_dec_o.rs1;
    assign rf_raddr2_p1_o.a1 = irb_dec_o.rs2;

    if (CHERIoTEn) begin
      rf_rdata2_t tmp_rdata2_a, tmp_rdata2_b;

      assign tmp_rdata2_a = update_rdata_1stage (
               .cheri_pmode    (cheri_pmode   ), 
               .rf_rdata2      (rf_rdata2_p0_i),
               .rf_raddr2      (rf_raddr2_p0_o),
               .trvk_en_i      (trvk_en_i     ),
               .trvk_clrtag_i  (trvk_clrtag_i ), 
               .trvk_addr_i    (trvk_addr_i   ) 
               );
         
      assign tmp_rdata2_b = update_rdata_1stage (
               .cheri_pmode    (cheri_pmode   ), 
               .rf_rdata2      (rf_rdata2_p1_i),
               .rf_raddr2      (rf_raddr2_p1_o),
               .trvk_en_i      (trvk_en_i     ),
               .trvk_clrtag_i  (trvk_clrtag_i ), 
               .trvk_addr_i    (trvk_addr_i   ) 
               );

      assign ira_op_rf_rdata2_o.d0 = reg2opcap(tmp_rdata2_a.d0);
      assign ira_op_rf_rdata2_o.d1 = reg2opcap(tmp_rdata2_a.d1); 
      assign irb_op_rf_rdata2_o.d0 = reg2opcap(tmp_rdata2_b.d0);
      assign irb_op_rf_rdata2_o.d1 = reg2opcap(tmp_rdata2_b.d1);
    end else begin
      assign ira_op_rf_rdata2_o.d0 = rf_rdata2_p0_i.d0;
      assign ira_op_rf_rdata2_o.d1 = rf_rdata2_p0_i.d1;
      assign irb_op_rf_rdata2_o.d0 = rf_rdata2_p1_i.d0;
      assign irb_op_rf_rdata2_o.d1 = rf_rdata2_p1_i.d1;
    end

  end // gen_dec_1stage

endmodule
