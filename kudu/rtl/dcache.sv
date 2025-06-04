// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// small inline data cache with low latency
//   - 1 cycle access time with small clk2q delay
//   - allow data forwarding
//
module dcache import super_pkg::*; (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // snooping lsue interface
  input  ir_dec_t              instr_i,
  input  logic                 lsu_req_i,    
  input  lsu_req_info_t        lsu_req_info_i,
  input  logic                 lsu_rdy_i,
  input  logic                 lsu_resp_valid_i,
  input  logic                 load_err_i,
  input  logic                 store_err_i,    
  input  logic [MemW-1:0]      data_rdata_i,   // QQQ let's worry about CHERIoT cap case later
  
  // data fwd interface
  input  waw_act_t             waw_act_i,
  output logic [31:0]          fwd_act_o,
  output pl_fwd_t              fwd_info_o
);
  localparam int unsigned addrLo = (MemW == 32) ? 2 : 3;

  function automatic logic [31:0] load_ext (logic sign_ext, logic[1:0] data_type, 
                                            logic[1:0] data_offset, logic [31:0] rdata);
    logic [31:0] result;

    logic [31:0] rdata_h_ext, rdata_b_ext;
    
    rdata_h_ext[15:0]  = data_offset[1] ? rdata[31:16] : rdata[15:0];
    rdata_h_ext[31:16] = sign_ext ? {16{rdata_h_ext[15]}} : 16'h0;

    case (data_offset)
      2'b00:   rdata_b_ext[7:0] = rdata[7:0];
      2'b01:   rdata_b_ext[7:0] = rdata[15:8];
      2'b10:   rdata_b_ext[7:0] = rdata[23:16];
      default: rdata_b_ext[7:0] = rdata[31:24];
    endcase

    rdata_b_ext[31:8] = sign_ext ? {23{rdata_b_ext[7]}} : 23'h0;

    case (data_type)
      2'b00: result = rdata;
      2'b01: result = rdata_h_ext;
      default: result = rdata_b_ext;
    endcase

    return result;
  endfunction

  function automatic logic [31:0] store_update (logic[1:0] data_type, logic [1:0] data_offset, 
                                                logic [31:0] reg_wdata, logic [31:0] old_mem_data); 
    logic [31:0] result;

    case (data_type)
      2'b00: result = reg_wdata;
      2'b01: begin
        if (data_offset[1]) result = {reg_wdata[15:0], old_mem_data[15:0]};
        else                result = {old_mem_data[31:16], reg_wdata[15:0]};
      end
      2'b10, 2'b11: begin
        if      (data_offset == 2'b00) result = {old_mem_data[31:8], reg_wdata[7:0]};
        else if (data_offset == 2'b01) result = {old_mem_data[31:16], reg_wdata[7:0], old_mem_data[7:0]};
        else if (data_offset == 2'b10) result = {old_mem_data[31:24], reg_wdata[7:0], old_mem_data[15:0]};
        else                                result = {reg_wdata[7:0], old_mem_data[23:0]};
      end
      default: result = reg_wdata;
    endcase
    return result;
  endfunction
  
  logic [MemW-1:0] cache_mem[4];
  logic [29:0]     tags[4];
  logic [3:0]      line_valid;

  logic [3:0]      rd_tag_match, wr_tag_match;
  logic            unaligned_access, unaligned_access_q;
  logic [MemW-1:0] line_rdata[4];
  logic            byp_tag_match;
  logic [MemW-1:0] line_wdata;
  logic [31:0]     cache_rdata, cache_rdata_ext;
  logic            waw_act_match;

  lsu_req_info_t   lsu_req_info_q;
  logic [3:0]      replace_sel, lfsr_sel_q;
  logic [3:0]      update_valid, update_invalid;
  logic            update_full_word;
  logic [MemW-1:0] cache_wdata[4];


  //
  //  Cache read side (data forwarding for load instructions)
  //

  for (genvar i=0; i<4; i++) begin : gen_cache_match
    assign rd_tag_match[i]  = line_valid[i] & (lsu_req_info_i.addr[31:addrLo] == tags[i]);
    //assign line_rdata[i] = cache_mem[i][lsu_req_info_i.addr[3:2]] & {32{rd_tag_match[i]}};
    assign line_rdata[i] = cache_mem[i] & {MemW{rd_tag_match[i]}};
  end

  // bypass/forward wdata to the new load instruction (full word write only)
  assign byp_tag_match  = ~lsu_req_info_q.rf_we & 
                          (lsu_req_info_i.addr[31:addrLo] == lsu_req_info_q.addr[31:addrLo]) & 
                          (lsu_req_info_q.data_type == 2'b00);
  assign line_wdata  = lsu_req_info_q.wdata & {MemW{byp_tag_match}};

  assign cache_rdata = line_rdata[0] | line_rdata[1] | line_rdata[2] | line_rdata[3] | line_wdata;

  // generate return register content based on cache read data and instruction request type
  assign cache_rdata_ext = load_ext(lsu_req_info_i.sign_ext, lsu_req_info_i.data_type, 
                                    lsu_req_info_i.addr[1:0], cache_rdata);


  // unaligned 32-bit or 16-bit accesses
  // let's not include those in the cache load case to simplif things a little
  assign unaligned_access = ((lsu_req_info_i.data_type==2'b00) && (lsu_req_info_i.addr[1:0]!=2'b00)) ||
                            ((lsu_req_info_i.data_type==2'b01) && (lsu_req_info_i.addr[0]  !=1'b0)); 

  assign waw_act_match =  (waw_act_i.valid[0] && (waw_act_i.rd0 == fwd_info_o.addr1)) || 
                          (waw_act_i.valid[1] && (waw_act_i.rd1 == fwd_info_o.addr1));
 
  assign fwd_act_o[0] = 1'b0;
  for (genvar i = 1; i < 32; i++) begin : gen_fwd_o
    assign fwd_act_o[i] = fwd_info_o.valid[1] && (fwd_info_o.addr1 == i);
  end 

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fwd_info_o <= NULL_PL_FWD;
    end else begin
      fwd_info_o.valid[0] <= 1'b0;
      fwd_info_o.addr0    <= 32'h0;  
      fwd_info_o.data0    <= 32'h0;  
  
      if (lsu_req_i & lsu_rdy_i & lsu_req_info_i.rf_we & ~unaligned_access & (|{rd_tag_match, byp_tag_match})) 
        fwd_info_o.valid[1] <= 1'b1;
      else if ((lsu_req_i & lsu_rdy_i) || waw_act_match)
        fwd_info_o.valid[1] <= 1'b0;

      if (lsu_req_i & lsu_rdy_i) begin
        fwd_info_o.addr1  <= instr_i.rd;
        fwd_info_o.data1  <= cache_rdata_ext;
      end
    end
  end

  //
  //  Cache update side
  //

  // Cache replacement on the response side (same time for both load/store)

  // if no match, simply randomly replace a line (most of cases there should be no empty lines)
  assign replace_sel = (|wr_tag_match) ? 0 : lfsr_sel_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lsu_req_info_q     <= NULL_LSU_REQ_INFO;
      unaligned_access_q <= 1'b0;
    end else begin
      if (lsu_req_i & lsu_rdy_i) begin 
        lsu_req_info_q     <= lsu_req_info_i;
        unaligned_access_q <= unaligned_access;
      end
    end
  end

  assign update_full_word = lsu_req_info_q.rf_we | (lsu_req_info_q.data_type == 2'b00);

  for (genvar i=0; i<4; i++) begin : gen_cache_line
    logic resp_good, resp_bad;

    assign resp_good = lsu_resp_valid_i & ~(load_err_i | store_err_i | unaligned_access_q);
    assign resp_bad  = lsu_resp_valid_i & (load_err_i | store_err_i | unaligned_access_q);

    assign wr_tag_match[i]   = line_valid[i] & (lsu_req_info_q.addr[31:addrLo] == tags[i]);
    // update cases:
    // 1: resp_good, tag match, 
    //    - either update_full_word or partial replace
    // 2: resp_good, no tag match, random replacement
    //    - subcase 1: full_word, validate
    //    - subcase 2: no full word, invalidate
    // 3: resp_bad, tag_match, invalidate
    // 4: resp_bad, no tag match, do nothing

    assign update_valid[i]   = resp_good & (wr_tag_match[i] | (replace_sel[i] & update_full_word));
    assign update_invalid[i] = (resp_bad  & wr_tag_match[i]) | (resp_good & replace_sel[i] & ~update_full_word);

    // rmw version of mem data for byte/halfword writes
    assign cache_wdata[i] = store_update (lsu_req_info_q.data_type, lsu_req_info_q.addr[1:0], 
                                          lsu_req_info_q.wdata, cache_mem[i]);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        line_valid[i] <= 1'b0;
        tags[i]       <= 0;
        cache_mem[i]  <= 0;
      end else begin
        // if unaligned access we just invalidate all lines to avoid being inconsistent
        if (update_valid[i]) begin
          line_valid[i] <= 1'b1;
          tags[i]       <= lsu_req_info_q.addr[31:addrLo];
          cache_mem[i]  <= lsu_req_info_q.rf_we ? data_rdata_i : cache_wdata[i];
        end else if (update_invalid[i]) begin
          line_valid[i] <= 1'b0;
        end
      end
    end
   
    //for (genvar j=0; j<4; j++) begin : gen_cache_word
    //  always_ff @(posedge clk_i or negedge rst_ni) begin
    //    if (!rst_ni) begin
    //      cache_mem[i][j] <= 0;
    //    end else begin
    //      if (update_valid[i] && (lsu_req_info_q.addr[3:2] == j)) 
    //        cache_mem[i][j] <= lsu_req_info_q.rf_we ? data_rdata_i : lsu_req_info_q.wdata;
    //    end
    //  end
    //end  // gen_cache_byte

  end  // gen_cache_line

  // small LFSR to generated pseudo-random replacement index
  logic [4:0] lfsr5;
  logic [7:0] lfsr8;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin 
      lfsr5      <= 5'h01;
      lfsr8      <= 8'hff;
      lfsr_sel_q <= 2'b00;
    end else begin
      // Feedback polynomial taps (x^5 + x^3 +  1) 
      lfsr5 <= {lfsr5[3:0], 1'b0} ^ ({5{lfsr5[4]}} & 5'b01001);
      // Feedback polynomial taps (x^8 + x^6 + x^5 + x^4 + 1) 
      lfsr8 <= {lfsr8[6:0], 1'b0} ^ ({8{lfsr8[7]}} & 8'b01110001);

      case ({lfsr5[0], lfsr8[0]})
        2'b00: lfsr_sel_q <= 4'b0001;
        2'b01: lfsr_sel_q <= 4'b0010;
        2'b10: lfsr_sel_q <= 4'b0100;
        2'b11: lfsr_sel_q <= 4'b1000;
        default: lfsr_sel_q <= 4'b0001;
      endcase
    end
  end

endmodule
