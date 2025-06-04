// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */

module load_store_unit import super_pkg::*; import cheri_pkg::*; import csr_pkg ::*; #(
  parameter bit          CHERIoTEn = 1'b0      
)(
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic            cheri_pmode_i,
                          
  // data memory interface       
  output logic            data_req_o,
  output logic            data_is_cap_o,
  input  logic            data_gnt_i,
  input  logic            data_rvalid_i,
  input  logic            data_err_i,
  input  logic            data_pmp_err_i,
                          
  output logic [31:0]     data_addr_o,
  output logic            data_we_o,
                          
  output logic [3:0]      data_be_o,
  output logic [MemW-1:0] data_wdata_o,
  input  logic [MemW-1:0] data_rdata_i,

  // signals to/from EX stage
  input  logic            lsu_req_i,    
  input  lsu_req_info_t   lsu_req_info_i,

  output logic            lsu_req_done_o,
                          
  output logic            lsu_resp_valid_o,
  output logic            lsu_resp_err_o,
  output pl_out_t         lsu_resp_info_o,
  output logic [31:0]     addr_last_o,    
  
  // downstream backpressure input
  input  logic            ds_rdy_i,

  // exception signals    
                          
  output logic            busy_o,
  output logic            perf_load_o,
  output logic            perf_store_o
);


  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_q, addr_last_d;

  logic         addr_update;
  logic         ctrl_update;
  logic         rdata_update;
  logic [31:8]  rdata_q;
  logic [1:0]   rdata_offset_q;

  logic [1:0]   data_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [MemW-1:0] data_wdata;

  logic [31:0]  data_rdata_ext;

  logic [32:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_q, handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_q, pmp_err_d;
  logic         lsu_err_q, lsu_err_d;
  logic         data_or_pmp_err;
  logic         cheri_err_d, cheri_err_q;

  logic         outstanding_resp_q, resp_wait;
  logic         lsu_resp_valid;
  logic         lsu_go;
  logic         addr_incr_req;
  logic         cheri_pmode;

  lsu_req_info_t   lsu_req_info_q;
  pl_out_t         lsu_resp_info;
  logic [5:0]      lsu_err_mcause;
  logic [31:0]     lsu_err_mtval;
  logic [RegW-1:0] lsu_rdata;    
 

  ls_fsm_e ls_fsm_cs, ls_fsm_ns;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  assign data_addr   = handle_misaligned_q ? (lsu_req_info_q.addr + {addr_incr_req, 2'b00}) : lsu_req_info_i.addr; 
  assign data_offset = (cheri_pmode & lsu_req_info_i.is_cap) ? 2'b00 : data_addr[1:0];


  ///////////////////
  // BE generation //
  ///////////////////

  always_comb begin
    if (cheri_pmode & lsu_req_info_i.is_cap)
      data_be = 4'b1111;        // caps are always word aligned
    else begin
      unique case (lsu_req_info_i.data_type) // Data type 00 Word, 01 Half word, 11,10 byte
        2'b00: begin // Writing a word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b1111;
              2'b01:   data_be = 4'b1110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0000; // this is not used, but included for completeness
              2'b01:   data_be = 4'b0001;
              2'b10:   data_be = 4'b0011;
              2'b11:   data_be = 4'b0111;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end
        end

        2'b01: begin // Writing a half word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0011;
              2'b01:   data_be = 4'b0110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            data_be = 4'b0001;
          end
        end

        2'b10,
        2'b11: begin // Writing a byte
          unique case (data_offset)
            2'b00:   data_be = 4'b0001;
            2'b01:   data_be = 4'b0010;
            2'b10:   data_be = 4'b0100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end

        default:     data_be = 4'b1111;
      endcase // case (lsu_req_info_i.data_type)
    end  // if lsu_cap
  end

  /////////////////////
  // WData alignment //
  /////////////////////

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses here
  logic [1:0]  wdata_offset;
  logic [31:0] wdata_int;

  always_comb begin
     wdata_offset = lsu_req_info_i.addr[1:0];
     unique case (wdata_offset)
       2'b00:   wdata_int = lsu_req_info_i.wdata[31:0];
       2'b01:   wdata_int = {lsu_req_info_i.wdata[23:0], lsu_req_info_i.wdata[31:24]};
       2'b10:   wdata_int = {lsu_req_info_i.wdata[15:0], lsu_req_info_i.wdata[31:16]};
       2'b11:   wdata_int = {lsu_req_info_i.wdata[ 7:0], lsu_req_info_i.wdata[31: 8]};
       default: wdata_int = lsu_req_info_i.wdata[31:0];
     endcase // case (wdata_offset)
   end

  if (CHERIoTEn) begin
    assign data_wdata = lsu_req_info_i.is_cap ? lsu_req_info_i.wdata: {33'h0, wdata_int[31:0]};
  end else begin
    assign data_wdata = wdata_int[31:0];
  end

  /////////////////////
  // RData alignment //
  /////////////////////

  // register for unaligned rdata
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q <= '0;
    end else if (rdata_update) begin
      rdata_q <= data_rdata_i[31:8];
    end
  end

  // registers for transaction control (response side)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_offset_q  <= 2'h0;
    end else if (ctrl_update) begin
        rdata_offset_q  <= data_offset;
    end
  end

  // registers for transaction control
  // Store last address for mtval + AGU for misaligned transactions.  Do not update in case of
  // errors, mtval needs the (first) failing address.  Where an aligned access or the first half of
  // a misaligned access sees an error provide the calculated access address. For the second half of
  // a misaligned access provide the word aligned address of the second half.
  assign addr_last_d = addr_incr_req ? data_addr_w_aligned : data_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_last_q <= '0;
    end else if (addr_update) begin
      addr_last_q <= addr_last_d;
    end
  end

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {1'b0, data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {1'b0, data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {1'b0, data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext =  data_rdata_i[31:0];
    endcase
  end

  ////////////////////
  // Sign extension //
  ////////////////////

  // sign extension for half words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
        end
      end

      2'b01: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
        end
      end

      2'b10: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
        end
      end

      2'b11: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
        end
      end

      default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
        end
      end

      2'b01: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
        end
      end

      2'b10: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
        end
      end

      2'b11: begin
        if (!lsu_req_info_q.sign_ext) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
        end
      end

      default: rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (lsu_req_info_q.data_type)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
      default:     data_rdata_ext = rdata_w_ext;
    endcase // case (data_type_q)
  end

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =  ~lsu_req_info_i.is_cap & ( 
      ((lsu_req_info_i.data_type == 2'b00) && (data_offset != 2'b00)) || // misaligned word access
      ((lsu_req_info_i.data_type == 2'b01) && (data_offset == 2'b11)));   // misaligned half-word access

  // FSM
  always_comb begin
    ls_fsm_ns       = ls_fsm_cs;

    data_req_o          = 1'b0;
    addr_incr_req       = 1'b0;
    handle_misaligned_d = handle_misaligned_q;
    pmp_err_d           = pmp_err_q;
    lsu_err_d           = lsu_err_q;
    cheri_err_d         = 1'b0;

    addr_update         = 1'b0;
    ctrl_update         = 1'b0;
    rdata_update        = 1'b0;

    perf_load_o         = 1'b0;
    perf_store_o        = 1'b0;

    lsu_go              = 1'b0;

    unique case (ls_fsm_cs)

      IDLE: begin
        pmp_err_d   = 1'b0;

        if (lsu_req_i & ~resp_wait & ds_rdy_i) begin
          data_req_o     = ~lsu_req_info_i.cheri_err;
          pmp_err_d      = data_pmp_err_i;
          lsu_err_d      = 1'b0;
          perf_load_o    = lsu_req_info_i.rf_we;
          perf_store_o   = ~lsu_req_info_i.rf_we;
          lsu_go         = 1'b1;         // decision to move forward with a request

          if (lsu_req_info_i.cheri_err) begin
            ls_fsm_ns           = IDLE;
            cheri_err_d         = 1'b1;
          end else if (data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            handle_misaligned_d = split_misaligned_access;
            ls_fsm_ns           = split_misaligned_access ? WAIT_RVALID_MIS : IDLE;
          end else begin
            ls_fsm_ns           = split_misaligned_access ? WAIT_GNT_MIS    : WAIT_GNT;
          end
        end
      end

      WAIT_GNT_MIS: begin
        data_req_o = 1'b1;
        // data_pmp_err_i is valid during the address phase of a request. An error will block the
        // external request and so a data_gnt_i might never be signalled. The registered version
        // pmp_err_q is only updated for new address phases and so can be used in WAIT_GNT* and
        // WAIT_RVALID* states
        if (data_gnt_i || pmp_err_q ) begin
          addr_update         = 1'b1;
          ctrl_update         = 1'b1;
          handle_misaligned_d = 1'b1;
          ls_fsm_ns           = WAIT_RVALID_MIS;
        end
      end

      WAIT_RVALID_MIS: begin
        // push out second request
        data_req_o = 1'b1;
        // tell ID/EX stage to update the address
        addr_incr_req = 1'b1;

        // first part rvalid is received, or gets a PMP error
        if (data_rvalid_i || pmp_err_q) begin
          // Update the PMP error for the second part
          pmp_err_d = data_pmp_err_i;
          // Record the error status of the first part
          lsu_err_d = data_err_i | pmp_err_q;
          // Capture the first rdata for loads
          rdata_update = lsu_req_info_q.rf_we;
          // If already granted, wait for second rvalid
          ls_fsm_ns = data_gnt_i ? IDLE : WAIT_GNT;
          // Update the address for the second part, if no error
          addr_update = data_gnt_i & ~(data_err_i | pmp_err_q);
          // clear handle_misaligned if second request is granted
          handle_misaligned_d = ~data_gnt_i;
        end else begin
          // first part rvalid is NOT received
          if (data_gnt_i) begin
            // second grant is received
            ls_fsm_ns = WAIT_RVALID_MIS_GNTS_DONE;
            handle_misaligned_d = 1'b0;
          end
        end
      end

      WAIT_GNT: begin
        // tell ID/EX stage to update the address
        addr_incr_req = handle_misaligned_q;
        data_req_o      = 1'b1;
        if (data_gnt_i || pmp_err_q) begin
          ctrl_update         = 1'b1;
          // Update the address, unless there was an error
          addr_update         = ~lsu_err_q;
          ls_fsm_ns           = IDLE;
          handle_misaligned_d = 1'b0;
        end
      end

      WAIT_RVALID_MIS_GNTS_DONE: begin
        // tell ID/EX stage to update the address (to make sure the
        // second address can be captured correctly for mtval and PMP checking)
        addr_incr_req = 1'b1;
        // Wait for the first rvalid, second request is already granted
        if (data_rvalid_i) begin
          // Update the pmp error for the second part
          pmp_err_d = data_pmp_err_i ;
          // The first part cannot see a PMP error in this state
          lsu_err_d = data_err_i;
          // Now we can update the address for the second part if no error
          addr_update = ~data_err_i;
          // Capture the first rdata for loads
          rdata_update = lsu_req_info_q.rf_we;
          // Wait for second rvalid
          ls_fsm_ns = IDLE;
        end
      end

      default: begin
        ls_fsm_ns = IDLE;
      end
    endcase
  end

  // hold off pipeline if an error occurred
  assign resp_wait = outstanding_resp_q & (~lsu_resp_valid | data_or_pmp_err);

  // we assume ctrl will be held till req_done asserted 
  // (once req captured in IDLE, it can be deasserted)
  logic lsu_req_done;

  assign lsu_req_done    = (lsu_go | (ls_fsm_cs != IDLE)) & (ls_fsm_ns == IDLE);
  assign lsu_req_done_o  = lsu_req_done;

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ls_fsm_cs           <= IDLE;
      handle_misaligned_q <= '0;
      pmp_err_q           <= '0;
      lsu_err_q           <= '0;
      cheri_err_q         <= 1'b0;
      outstanding_resp_q  <= 1'b0;
      lsu_req_info_q      <= NULL_LSU_REQ_INFO;
    end else begin
      ls_fsm_cs           <= ls_fsm_ns;
      handle_misaligned_q <= handle_misaligned_d;
      pmp_err_q           <= pmp_err_d;
      lsu_err_q           <= lsu_err_d;
      cheri_err_q         <= cheri_err_d;

      if (lsu_go)
        lsu_req_info_q  <= lsu_req_info_i;

      if (lsu_go)
        outstanding_resp_q <= 1'b1;
      else if (lsu_resp_valid)
        outstanding_resp_q <= 1'b0;

    end
  end

  // cheri checking at response side (for earlyLoads)
  logic cheri_ls_err;
  logic ls_align_err_only;
  logic [4:0] cheri_err_cause;

  if (CHERIoTEn) begin : gen_resp_chk
    always_comb begin
      logic [7:0] cheri_check_result;

      cheri_check_result = ~cheri_pmode ? 7'h0 : 
                           cheri_ls_check (lsu_req_info_q.lschk_info, lsu_req_info_q.addr,
                                           lsu_req_info_q.rf_we, lsu_req_info_q.is_cap, 
                                           lsu_req_info_q.data_type);
      ls_align_err_only  = cheri_check_result[2] & (~lsu_req_info_q.cheri_err | lsu_req_info_q.align_err_only);
      cheri_ls_err       = cheri_check_result[0] | lsu_req_info_q.cheri_err; 

      if (lsu_req_info_q.cheri_err) 
        cheri_err_cause = lsu_req_info_q.cheri_cause;
      else 
        cheri_err_cause = cheri_check_result[7:3];
    end
  end else begin : gen_no_resp_chk
    assign cheri_ls_err    = 1'b0;
    assign cheri_err_cause = 5'h0;
  end

  // load/store error mcause/mtval encoding
  always_comb begin
    lsu_err_mcause = 6'h0;
    lsu_err_mtval  = 32'h0;

    if (cheri_ls_err) begin
      if (ls_align_err_only) begin
        lsu_err_mcause = EXC_CAUSE_LOAD_ADDR_MISALIGN;
        lsu_err_mtval  = addr_last_q;
      end else begin
        // CHERIoT requires rs1 as part of MTVAL info for cheri faults
        lsu_err_mcause = EXC_CAUSE_CHERI_FAULT;
        lsu_err_mtval  = {22'h0, lsu_req_info_q.rs1, cheri_err_cause};
      end
    end else if (data_or_pmp_err) begin
      lsu_err_mcause = EXC_CAUSE_LOAD_ACCESS_FAULT;
      lsu_err_mtval  = addr_last_q;
    end
  end

  if (CHERIoTEn) begin : gen_cap_rd
    assign lsu_rdata = lsu_req_info_q.is_cap ? mem2regcap(data_rdata_i, lsu_req_info_q.clrperm) : {33'h0, data_rdata_ext};
  end else begin : gen_no_cap_rd
    assign lsu_rdata = data_rdata_ext;
  end

  /////////////
  // Outputs //
  /////////////

  logic all_resp;
  assign data_or_pmp_err    = lsu_err_q | data_err_i | pmp_err_q | cheri_ls_err ;

  assign all_resp           = data_rvalid_i | pmp_err_q | (cheri_pmode & cheri_err_q);
  assign lsu_resp_valid     = all_resp & (ls_fsm_cs == IDLE) ;
  assign lsu_resp_valid_o   = lsu_resp_valid;
  
  assign lsu_resp_err_o     = data_or_pmp_err & lsu_resp_valid;
  assign lsu_resp_info_o    =  lsu_resp_info;

  // output to register file
  assign lsu_resp_info.we     = lsu_req_info_q.rf_we;
  assign lsu_resp_info.wrsv   = lsu_req_info_q.rf_we;
  assign lsu_resp_info.waddr  = lsu_req_info_q.rd;
  assign lsu_resp_info.pc     = lsu_req_info_q.pc;
  assign lsu_resp_info.wdata  = lsu_rdata;
  assign lsu_resp_info.err    = data_or_pmp_err;
  assign lsu_resp_info.mcause = lsu_err_mcause;
  assign lsu_resp_info.mtval  = lsu_err_mtval;
  assign lsu_resp_info.is_cap = lsu_req_info_q.is_cap;
  
  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;

  assign data_wdata_o  = data_wdata;
  assign data_we_o     = ~lsu_req_info_i.rf_we;
  assign data_be_o     = data_be;

  assign data_is_cap_o = lsu_req_info_i.is_cap;

  assign addr_last_o   = addr_last_q;
  assign busy_o = (ls_fsm_cs != IDLE);

endmodule
