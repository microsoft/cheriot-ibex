// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Multi-function pipeline
//  - Multiplication & division
//  - CSR/SCR read/write
//  - CHERIoT cjalr
//  - CHERIoT csetbounds*
//

module mult_pipeline import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; # (
  parameter bit NoMult    = 1'b0,
  parameter bit CHERIoTEn = 1'b0,
  parameter bit UseDWMult = 1'b0
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 cheri_pmode_i,
  input  logic                 flush_i,

  // upstream (issuer) side interface
  input  logic                 us_valid_i,
  output logic                 multpl_rdy_o,
  input  logic                 sel_ira_i,
  input  ir_dec_t              ira_dec_i,
  input  ir_dec_t              irb_dec_i,
  input  full_data2_t          ira_full_data2_i,
  input  full_data2_t          irb_full_data2_i,
  input  logic                 pcc_asr_i,
  input  waw_act_t             waw_act_i,

  output logic [31:0]          fwd_act_o,
  output pl_fwd_t              fwd_info_o,
            
  // downstream (commit) side interface
  input  logic                 ds_rdy_i,
  output logic                 multpl_valid_o,
  output pl_out_t              multpl_output_o,

  // CSR r/w interface
  output logic                 csr_access_o,
  output logic                 csr_cheri_o,
  output logic                 csr_op_en_o,
  output csr_op_e              csr_op_o,
  output csr_num_e             csr_addr_o,
  output logic [RegW-1:0]      csr_wdata_o,
  input  logic [RegW-1:0]      csr_rdata_i,
  input  logic                 illegal_csr_insn_i,      // access to non-existent CSR,
  input  logic                 csr_mstatus_mie_i,
  input  pcc_cap_t             pcc_cap_i,
  output pcc_cap_t             pcc_cap_o,
  output logic                 cheri_pcc_set_o,
  output logic                 csr_set_mie_o,           
  output logic                 csr_clr_mie_o           
);

  typedef struct packed {
    logic is_csr;
    logic is_cjalr;
    logic is_mult;
    logic is_div;
  } flags_t;

  typedef struct packed {
    flags_t          flags;
    cheri_op_t       cheri_op;
    logic            rf_we;
    logic [4:0]      rd;
    logic [OpW-1:0]  wdata;
    logic [31:0]     pc;
    logic            err;
    logic [5:0]      err_type; // bit 0: cheri ASR (0) or illegal csr (1)
    logic [31:0]     insn;
  } multpl_reg_t;

  localparam multpl_reg_t DEF_PL_REG = multpl_reg_t'(0);

  function automatic full_cap_t legalize_scr (logic is_scr, logic [4:0] scr_addr, full_cap_t cs1_fcap);
    full_cap_t result;
    result = cs1_fcap;

    if (scr_addr == CHERI_SCR_MTCC) begin
      // MTVEC/MTCC legalization (clear tag if checking fails)
      // note we don't reall need set_address checks here - it's only used to update temp fields
      //   so that RTL behavior would match sail
      result.addr    = {cs1_fcap.addr[31:2], 2'b00};
      if ((cs1_fcap.addr[1:0] != 2'b00) || ~cs1_fcap.perms[PERM_EX] || (cs1_fcap.otype != 0))
        result.valid = 1'b0;
    end else if (scr_addr == CHERI_SCR_MEPCC) begin
      // MEPCC legalization (clear tag if checking fails)
      result.addr    = {cs1_fcap.addr[31:1], 1'b0};
      if ((cs1_fcap.addr[0] != 1'b0) || ~cs1_fcap.perms[PERM_EX] || (cs1_fcap.otype != 0))
        result.valid = 1'b0;
    end

    return result;
  endfunction

  ir_dec_t     instr_dec;
  full_data2_t full_data2;     
  logic        ex2_valid, ex2_rdy;
  logic        wb_valid, wb_rdy;

  multpl_reg_t ex2_reg, wb_reg;
  multpl_reg_t ex1to2_reg, ex2wb_reg;

  logic        md_mult_en;
  logic        md_div_en;
  md_op_e      md_operator;
  logic  [1:0] md_signed_mode;
  logic [31:0] md_op_a;
  logic [31:0] md_op_b;
  logic [31:0] md_mult_result, md_div_result;
  logic        md_mult_valid, md_div_valid;

  logic        op_done, op_done_q;
  logic        ex2wb_valid;

  logic        ex2_fwd_ok;
  logic        wb_fwd_valid_d,  wb_fwd_valid_q;
  logic [4:0]  wb_fwd_rd;
  logic        cheri_pmode;

  logic [OpW-1:0]  ex1_result,  ex2_result;
  logic [RegW-1:0] ex1_csr_wdata;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  // select input
  assign instr_dec  = sel_ira_i ? ira_dec_i : irb_dec_i;
  assign full_data2 = sel_ira_i ? ira_full_data2_i : irb_full_data2_i;
  
  //
  // Data forwarding
  //

  assign fwd_act_o[0] = 1'b0;
  for (genvar i = 1; i < 32; i++) begin : gen_fwd_o
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) 
        fwd_act_o[i] <= 1'b0;
      else 
        fwd_act_o[i] <= wb_fwd_valid_d && (wb_fwd_rd == i);
    end
  end 


  assign fwd_info_o.valid  = {wb_fwd_valid_q, 1'b0};
  assign fwd_info_o.data0  = 32'h0;
  assign fwd_info_o.addr0  = 5'h0;
  assign fwd_info_o.data1  = wb_reg.wdata;
  assign fwd_info_o.addr1  = wb_reg.rd;

  // Muxing forwarded data  is done in the issuer

  //
  //  EX1 stage
  //   - multidiv (1st stage)
  //   - csetbounds (1st stage)
  //   - cjalr
  // 
  logic        ex1_is_csr, ex1_is_cjalr;
  logic        mult_sel, div_sel;
  opcode_e     opcode;
  logic [9:0]  func10;

  setbounds_req_t setbounds_req_d, setbounds_req_q;
  full_cap_t      ex1_tfcap_d, ex1_tfcap_q;
  logic           req_exact_d, req_exact_q;

  assign multpl_rdy_o = ex2_rdy;

  assign ex1_is_csr    = instr_dec.sysctl.csr || instr_dec.cheri_op.cscrrw;
  assign ex1_is_cjalr  = cheri_pmode & instr_dec.is_jalr;
  assign ex1_csr_wdata = instr_dec.insn[14] ? instr_dec.insn[19:15] : full_data2.d0[RegW-1:0];

  assign ex1_result    = ex1_csr_wdata; // only used by RV32 CSR instructions

  assign ex1to2_reg = '{'{ex1_is_csr, ex1_is_cjalr, mult_sel, div_sel},
                        instr_dec.cheri_op, instr_dec.rf_we, instr_dec.rd, 
                        ex1_result, instr_dec.pc, '0, '0, instr_dec.insn};  

  // decoding for multdiv
  assign opcode = opcode_e'(instr_dec.insn[6:0]);
  assign func10 = {instr_dec.insn[31:25], instr_dec.insn[14:12]};

  always_comb begin
    mult_sel       = 1'b0;
    div_sel        = 1'b0;
    md_operator    = MD_OP_MULL;
    md_signed_mode = 2'b00;
    
    if (opcode == OPCODE_OP) begin
      unique case (func10)
        {7'b000_0001, 3'b000} : begin  // mul
          mult_sel         = 1'b1;
          md_operator    = MD_OP_MULL;
          md_signed_mode = 2'b00;
        end
        {7'b000_0001, 3'b001}: begin // mulh
          mult_sel         = 1'b1;
          md_operator    = MD_OP_MULH;
          md_signed_mode = 2'b11;
        end
        {7'b000_0001, 3'b010}: begin // mulhsu
          mult_sel         = 1'b1;
          md_operator    = MD_OP_MULH;
          md_signed_mode = 2'b01;
        end
        {7'b000_0001, 3'b011}: begin // mulhu
          mult_sel         = 1'b1;
          md_operator    = MD_OP_MULH;
          md_signed_mode = 2'b00;
        end
        {7'b000_0001, 3'b100}: begin // div
          div_sel          = 1'b1;
          md_operator    = MD_OP_DIV;
          md_signed_mode = 2'b11;
        end
        {7'b000_0001, 3'b101}: begin // divu
          div_sel          = 1'b1;
          md_operator    = MD_OP_DIV;
          md_signed_mode = 2'b00;
        end
        {7'b000_0001, 3'b110}: begin // rem
          div_sel          = 1'b1;
          md_operator    = MD_OP_REM;
          md_signed_mode = 2'b11;
        end
        {7'b000_0001, 3'b111}: begin // remu
          div_sel          = 1'b1;
          md_operator    = MD_OP_REM;
          md_signed_mode = 2'b00;
        end
        default: ;

     endcase
    end
  end

  // mult/div starts in EX1, results captured in EX2
  assign md_mult_en      = us_valid_i & mult_sel & ex2_rdy;
  assign md_div_en       = us_valid_i & div_sel  & ex2_rdy;
  assign md_op_a         = full_data2.d0[31:0];
  assign md_op_b         = full_data2.d1[31:0];

  //  CHERIoT operations

  if (CHERIoTEn) begin
    logic [2:0]  seal_type;
    logic [31:0] pc_nxt;
    full_cap_t   cs1_fcap, cs2_fcap;
    full_cap_t   cjalr_tfcap;

    assign cs1_fcap = full_cap_t'(full_data2.d0);
    assign cs2_fcap = full_cap_t'(full_data2.d1);

    // cjlar operation    
    always_comb begin
      pc_nxt      = instr_dec.pc + (instr_dec.is_comp ? 2 : 4);
      seal_type   = csr_mstatus_mie_i ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD;

      cjalr_tfcap       = pcc2fullcap_lite(pcc_cap_i, pc_nxt);
      cjalr_tfcap.otype = (instr_dec.rd == 5'h1) ? seal_type : cjalr_tfcap.otype;

      csr_set_mie_o = us_valid_i & ex1_is_cjalr & ex2_rdy &
                      ((cs1_fcap.otype == OTYPE_SENTRY_IE_FWD) || (cs1_fcap.otype == OTYPE_SENTRY_IE_BKWD));
      csr_clr_mie_o = us_valid_i & ex1_is_cjalr & ex2_rdy &
                      ((cs1_fcap.otype == OTYPE_SENTRY_ID_FWD) || (cs1_fcap.otype == OTYPE_SENTRY_ID_BKWD));
    end

    // pc bound violation checked later
    // pcc only contains address bound/metadata, no need for set_addr
    assign pcc_cap_o       =  full2pcap(unseal_cap(cs1_fcap));  
    assign cheri_pcc_set_o = us_valid_i & ex1_is_cjalr & ex2_rdy;
    
    // csetbounds 1st stage & shared context flops
    always_comb begin: set_bounds_comb
      logic [31:0] newlen;
      logic        req_exact;
      logic [31:0] tmp_addr;
      
      if (ex1_is_csr) begin
        newlen      = cs1_fcap.addr;
        req_exact_d = 1'b0;
        ex1_tfcap_d = cs1_fcap;
      end else if (ex1_is_cjalr) begin
        newlen      = cs1_fcap.addr;
        req_exact_d = 1'b0;
        ex1_tfcap_d = cjalr_tfcap;
      end else if (instr_dec.cheri_op.csetbounds | instr_dec.cheri_op.csetboundsrndn) begin
        newlen      = cs2_fcap.addr;
        req_exact_d = 1'b0;
        ex1_tfcap_d = cs1_fcap;
      end else if (instr_dec.cheri_op.csetboundsex) begin
        newlen      = cs2_fcap.addr;
        req_exact_d = 1'b1;
        ex1_tfcap_d = cs1_fcap;
      end else if (instr_dec.cheri_op.csetboundsimm) begin
        newlen       = 32'(instr_dec.insn[31:20]);  // unsigned imm
        req_exact_d  = 1'b0;
        ex1_tfcap_d = cs1_fcap;
      end else if (instr_dec.cheri_op.crrl | instr_dec.cheri_op.cram) begin
        // crrl | cram
        newlen      = cs1_fcap.addr;
        req_exact_d = 1'b0;
        ex1_tfcap_d = NULL_FULL_CAP;
      end

      // csetbounds operation (1st stage)
      setbounds_req_d = prep_bound_req(ex1_tfcap_d, newlen);
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        setbounds_req_q  <= setbounds_req_t'(0);
        req_exact_q      <= 1'b0;
        ex1_tfcap_q      <= NULL_FULL_CAP;
      end else if (ex2_rdy) begin
        setbounds_req_q  <= setbounds_req_d;
        req_exact_q      <= req_exact_d;
        ex1_tfcap_q      <= ex1_tfcap_d; 
      end
    end
    

  end else begin

    assign csr_set_mie_o   = 1'b0;
    assign csr_clr_mie_o   = 1'b0;
    assign setbounds_req_q = setbounds_req_t'(0);
    assign req_exact_q     = 1'b0;
    assign ex1_tfcap_q     = NULL_FULL_CAP;
  end
  
  //
  // EX2 stage
  // - multidiv (2nd stage)
  // - csetbounds (2nd stage)
  // - csr read/write
  //

  logic        ex2_waw_match;
  logic        ex2_err; 
  logic [5:0]  ex2_err_type;


  assign ex2_rdy      = ~ex2_valid | (op_done & wb_rdy);
  assign op_done      = ex2_reg.flags.is_csr | ex2_reg.flags.is_cjalr | (|ex2_reg.cheri_op) | 
                        ex2_reg.flags.is_mult | (ex2_reg.flags.is_div & md_div_valid) | op_done_q;
  assign ex2wb_valid  = ex2_valid & op_done;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      ex2_valid  <= 1'b0;
      ex2_reg    <= DEF_PL_REG;
      op_done_q  <= 1'b0;
      ex2_fwd_ok <= 1'b0;
    end else begin
      if (flush_i) begin
        ex2_valid  <= 1'b0;
        ex2_fwd_ok <= 1'b0;
      end else if (ex2_rdy) begin 
        ex2_valid  <= us_valid_i;
        ex2_reg    <= ex1to2_reg;
        ex2_fwd_ok <= 1'b1;
      end else if (ex2_waw_match) begin
        ex2_fwd_ok <= 1'b0;
      end

      // latch op_done status in case wb is not ready
      if (flush_i) 
        op_done_q <= 1'b0;
      else if (ex2_rdy)
        op_done_q <= 1'b0;
      else if (op_done) 
        op_done_q <= 1'b1;
    end
  end

  assign ex2_waw_match = (waw_act_i.valid[0] && (waw_act_i.rd0 == ex2_reg.rd)) || 
                         (waw_act_i.valid[1] && (waw_act_i.rd1 == ex2_reg.rd));

  setbounds_out_t ex2_bounds;
  full_cap_t      ex2_tfcap; 
  full_cap_t      ex2_sa_fcap_in, ex2_sa_fcap_out;
  full_cap_t      scr_wcap_legalized;
  
  assign ex2_sa_fcap_in  = ex2_reg.flags.is_csr ? scr_wcap_legalized : ex1_tfcap_q;
  assign ex2_sa_fcap_out = set_address(ex2_sa_fcap_in, ex2_sa_fcap_in.addr); 

  // muxing the results from EX2
  always_comb begin
    cheri_op_t cheri_op;

    cheri_op    = ex2_reg.cheri_op;

    ex2_bounds = NULL_SETBOUNDS_OUT;
    ex2_tfcap  = ex2_bounds.fcap;
    ex2_result = md_mult_result;

    if (ex2_reg.flags.is_cjalr) begin 
      ex2_tfcap  = ex2_sa_fcap_out;
      ex2_result = ex2_tfcap[OpW-1:0];
    end else if (ex2_reg.flags.is_csr) begin 
      ex2_result = csr_rdata_i;
    end else if (ex2_reg.flags.is_mult) begin 
      ex2_result = md_mult_result;
    end else if (ex2_reg.flags.is_div) begin 
      ex2_result = md_div_result;
    end else if (cheri_op.csetbounds | cheri_op.csetboundsex | cheri_op.csetboundsimm | 
                 cheri_op.crrl | cheri_op.cram) begin
      ex2_bounds = set_bounds(ex1_tfcap_q, setbounds_req_q, req_exact_q);
      ex2_tfcap  = ex2_bounds.fcap;
      ex2_result = cheri_op.crrl ? ex2_bounds.rlen :
                   (cheri_op.cram ? ex2_bounds.maska : ex2_tfcap[OpW-1:0]);
    end else if (cheri_op.csetboundsrndn) begin
      ex2_bounds = set_bounds_rndn(ex1_tfcap_q, setbounds_req_q);
      ex2_tfcap  = ex2_bounds.fcap;
      ex2_result = ex2_tfcap[OpW-1:0];
    end
  end

  // CSR operations

  logic        csr_cheri, csr_cheri_err;
  logic        csr_cheri_asr_err, csr_cheri_always_ok;
  logic [31:0] ex2_insn;
  logic [4:0]  scr_addr;
  logic [11:0] csr_addr;

  assign csr_op_en_o  = ex2_valid & ex2_reg.flags.is_csr;
  assign csr_access_o = csr_op_en_o; 
  assign csr_wdata_o  = csr_cheri ? ex2_sa_fcap_out[RegW-1:0] : ex2_reg.wdata;
  assign csr_cheri    = ex2_reg.cheri_op.cscrrw;
  assign csr_cheri_o  = csr_cheri;

  assign scr_addr   = ex2_insn[24:20];
  assign csr_addr   = ex2_insn[31:20]; 
  assign ex2_insn   = ex2_reg.insn;
  assign csr_addr_o = csr_cheri ? csr_num_e'({7'h0, scr_addr}) : csr_num_e'(csr_addr); 

  // legalize SCR write value
  assign scr_wcap_legalized = legalize_scr(csr_cheri, scr_addr, ex1_tfcap_q);

  // check CHERIoT CSR/SCR access permission
  assign csr_cheri_always_ok = ~csr_cheri & (((ex2_insn[31:28] == 4'hb) || (ex2_insn[31:28] == 4'hc)) && 
                               ((ex2_insn[27] == 1'b0) || (ex2_insn[26:25] == 2'b00)));
  assign csr_cheri_asr_err   = cheri_pmode & ~pcc_asr_i & ~csr_cheri_always_ok;
  
  assign ex2_err      = ex2_reg.flags.is_csr ? illegal_csr_insn_i | csr_cheri_asr_err : 1'b0;
  //  ASR error for SCR access: fill in scr address. ASR error for CSR: use zero
  assign ex2_err_type = {(csr_cheri ? scr_addr : 0), illegal_csr_insn_i}; 

  always_comb begin
    logic        rs1_is_zero;
 
    rs1_is_zero = (ex2_insn[19:15] == '0);

    if (csr_cheri) begin
      csr_op_o = rs1_is_zero ? CSR_OP_READ : CSR_OP_WRITE;
    end else begin
      case (ex2_insn[13:12])
        2'b01:   csr_op_o = CSR_OP_WRITE;
        2'b10:   csr_op_o = rs1_is_zero ? CSR_OP_READ : CSR_OP_SET;
        2'b11:   csr_op_o = rs1_is_zero ? CSR_OP_READ : CSR_OP_CLEAR;
        default: csr_op_o = CSR_OP_READ;       // don't care case
      endcase
    end
  end

  //
  // WB stage
  //
  logic wb_waw_match;

  assign wb_rdy = ~wb_valid | ds_rdy_i;

  always_comb begin
    if (flush_i) begin
      wb_fwd_valid_d = 1'b0;
      wb_fwd_rd      = 0;
    end else if (wb_rdy) begin
      wb_fwd_valid_d = ex2wb_valid & ex2_reg.rf_we  && (ex2_reg.rd != 0) & ~ex2_waw_match & ex2_fwd_ok;
      wb_fwd_rd      = ex2_reg.rd;
    end else if (wb_waw_match) begin
      wb_fwd_valid_d = 1'b0;
      wb_fwd_rd      = wb_reg.rd;
    end else begin
      wb_fwd_valid_d = wb_fwd_valid_q;
      wb_fwd_rd      = wb_reg.rd;
    end

   ex2wb_reg          = ex2_reg;
   ex2wb_reg.wdata    = ex2_result;
   ex2wb_reg.err      = ex2_err;
   ex2wb_reg.err_type = ex2_err_type;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      wb_valid       <= 1'b0;
      wb_reg         <= DEF_PL_REG;
      wb_fwd_valid_q <= 1'b0;
    end else begin
      if (flush_i) begin
        wb_valid <= 1'b0;
      end else if (wb_rdy) begin 
        wb_valid <= ex2wb_valid;
        wb_reg   <= ex2wb_reg;
      end

      wb_fwd_valid_q <= wb_fwd_valid_d;
    end
  end

  assign wb_waw_match = (waw_act_i.valid[0] && (waw_act_i.rd0 == wb_reg.rd)) ||
                        (waw_act_i.valid[1] && (waw_act_i.rd1 == wb_reg.rd));

  // Output to commit 
  assign multpl_valid_o         = wb_valid;
  assign multpl_output_o.we     = wb_reg.rf_we;
  assign multpl_output_o.wrsv   = wb_reg.rf_we & wb_fwd_valid_q;
  assign multpl_output_o.waddr  = wb_reg.rd;
  assign multpl_output_o.wdata  = wb_reg.wdata;
  assign multpl_output_o.err    = wb_reg.err;
  assign multpl_output_o.mcause = wb_reg.err_type[0] ? EXC_CAUSE_ILLEGAL_INSN : EXC_CAUSE_CHERI_FAULT;
  assign multpl_output_o.mtval  = wb_reg.err_type[0] ? 32'h0 : {21'h0, 1'b1, wb_reg.err_type[5:1], 5'h18};  
  assign multpl_output_o.pc     = wb_reg.pc;   

  //
  //  MultDiv function instantiation
  //

  if (!NoMult) begin
    multdiv32 #(.UseDWMult(UseDWMult))  multdiv32_i (
      .clk_i               (clk_i              ),
      .rst_ni              (rst_ni             ),
      .mult_en_i           (md_mult_en         ),
      .div_en_i            (md_div_en          ),
      .operator_i          (md_operator        ),
      .signed_mode_i       (md_signed_mode     ),
      .op_a_i              (md_op_a            ),
      .op_b_i              (md_op_b            ),
      .data_ind_timing_i   (1'b0               ),
      .mult_result_o       (md_mult_result     ),
      .div_result_o        (md_div_result      ),
      .mult_valid_o        (md_mult_valid      ),
      .div_valid_o         (md_div_valid       )
    );
  end else begin
    assign md_mult_valid  = 1'b1;
    assign md_div_valid   = 1'b1;
    assign md_mult_result = 32'h0;
    assign md_div_result = 32'h0;
  end

endmodule
