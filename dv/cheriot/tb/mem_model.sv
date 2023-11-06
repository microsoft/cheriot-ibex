// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// memory model with random gnt/rvalid waits 
//
module mem_model #(
  parameter DATA_GNT_WMAX = 3,
  parameter DATA_RESP_WMAX = 2,  
  parameter MEM_AW = 16,  
  parameter MEM_DW = 32  
)( 
  input  logic        clk,
  input  logic        rst_n,

  input  logic        data_req,
  input  logic        data_we,
  input  logic [3:0]  data_be,
  input  logic [31:0] data_addr,
  input  logic [MEM_DW-1:0] data_wdata,

  output logic        data_gnt,
  output logic        data_rvalid,
  output logic [MEM_DW-1:0] data_rdata,
  output logic        data_err
);
  //
  // simple unified memory system model
  reg   [MEM_DW-1:0] mem[0:2**MEM_AW-1];

  logic              mem_cs;
  logic              mem_we;
  logic        [3:0] mem_be;
  logic [MEM_DW-1:0] mem_din;
  logic [MEM_DW-1:0] mem_dout;
  logic [MEM_AW-1:0] mem_addr;

  logic              gnt_idle, nxt_gnt_idle;
  logic              resp_idle, nxt_resp_idle;
  logic        [3:0] gnt_waits, resp_waits;
  logic        [3:0] gnt_wait_cnt, resp_wait_cnt;
  logic        [3:0] rand1, rand2;

  logic              pnd_gnt_data_q;
  logic              pnd_gnt_data;

  logic              data_gnt_q;

  assign data_err = 1'b0;       // QQQ for now

  // 
  // Arbitration and grant stage
  //

  // IDLE is the state 
  //    -- look at incoming requests and make arbitration decisions
  //    -- decides to wait or not
  assign pnd_gnt_data  = gnt_idle & data_req;  

  // grant to bus master - note this also serves as requests to the next stage
  assign data_gnt    = (gnt_idle & nxt_gnt_idle & pnd_gnt_data) |
                       ((~gnt_idle) & nxt_gnt_idle & pnd_gnt_data_q); 
 
  assign gnt_waits  = rand1;
  assign resp_waits = rand2;

  always_comb begin
    if (gnt_idle && data_req && ((~resp_idle) || (gnt_waits != 0)))
      nxt_gnt_idle = 1'b0;
    else if ((!gnt_idle) && resp_idle && (gnt_wait_cnt == 0)) 
      nxt_gnt_idle = 1'b1;
    else
      nxt_gnt_idle = gnt_idle;
  end

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      gnt_idle       <= 1'b1;
      gnt_wait_cnt    <= 4'h0;
      pnd_gnt_data_q  <= 1'b0;
    end else begin
      gnt_idle <= nxt_gnt_idle;
      
      if (pnd_gnt_data && (!nxt_gnt_idle) && (gnt_waits != 0))
        gnt_wait_cnt <= gnt_waits - 1;
      else if (gnt_wait_cnt != 0)
        gnt_wait_cnt <= gnt_wait_cnt - 1;

      if (gnt_idle & (~nxt_gnt_idle)) begin
        pnd_gnt_data_q  <= pnd_gnt_data;
      end
     
    end
  end
  
  // 
  //  Response stage
  //

  assign data_rdata   = mem_dout & {33{data_rvalid}}; 

  always_comb begin
    if (resp_idle && data_gnt && (resp_waits != 0))
      nxt_resp_idle = 1'b0;
    else if ((!resp_idle) && (resp_wait_cnt == 0)) 
      nxt_resp_idle = 1'b1;
    else
      nxt_resp_idle = resp_idle;
  end

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      resp_idle       <= 1'b1;
      resp_wait_cnt   <= 4'h0;
      data_gnt_q      <= 1'b0;
      data_rvalid     <= 1'b0;
    end else begin
      resp_idle <= nxt_resp_idle;

      if (resp_idle && (!nxt_resp_idle))
        resp_wait_cnt <= resp_waits - 1;
      else if (resp_wait_cnt != 0)
        resp_wait_cnt <= resp_wait_cnt - 1;

      if (resp_idle) begin
        data_gnt_q  <= data_gnt;
      end 

      if (resp_idle & nxt_resp_idle & data_gnt)
        data_rvalid  <= 1'b1;
      else if ((~resp_idle) & nxt_resp_idle & data_gnt_q) 
        data_rvalid  <= 1'b1;
      else
        data_rvalid  <= 1'b0;

    end
  end

  // generate enough randoms per clock cycle 
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      rand1 <= 0;
      rand2 <= 0;
    end else begin
      rand1 <= $urandom() % DATA_GNT_WMAX;
      rand2 <= $urandom() % DATA_RESP_WMAX;    
    end
  end


  // memory pin muxing
  // note we don't register this - by protocol the requester hold the value till granted
  assign mem_cs   = data_gnt;
  assign mem_we   = data_gnt & data_we;
  assign mem_be   = data_gnt ? data_be : 4'hf;
  assign mem_din  = data_wdata;
  assign mem_addr = data_addr[MEM_AW+1:2];  

  always @(posedge clk) begin
    if (mem_cs && mem_we) begin
      if(mem_be[0])
        mem[mem_addr][7:0]  <= mem_din[7:0];
      if(mem_be[1])
        mem[mem_addr][15:8] <= mem_din[15:8];
      if(mem_be[2])
        mem[mem_addr][23:16] <= mem_din[23:16];
      if(mem_be[3])
        mem[mem_addr][31:24] <= mem_din[31:24];

      // valid tag bit for caps - only allow to update for word accesses, where bit[32] is taken 
      // care of by CPU, otherwise clear the valid bit.
      //  - if the physical memory doesn't support BE for bit[32], then needs RMW or 
      //    separate mem for tag bits..
       // - only makes sure data accesses can't modify capabilities but could still read..
      // is this sufficent for cheri - QQQ? 
      //  - the original cheri ask is to qualify memory accesses based on the tag bit, which requires RMW
      if (MEM_DW == 33) begin
        if (&mem_be)  mem[mem_addr][MEM_DW-1]  <= mem_din[MEM_DW-1];
        else           mem[mem_addr][MEM_DW-1]  <= 1'b0;
      end
        
    end
    else if (mem_cs)
      mem_dout <= mem[mem_addr];  
  end


endmodule
