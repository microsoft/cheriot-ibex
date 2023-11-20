// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// memory model with random gnt/rvalid waits 
//
module mem_model #(
  parameter bit          ERR_INJECT = 1'b0,
  parameter int unsigned GNT_WMAX   = 2,
  parameter int unsigned RESP_WMAX  = 1,  
  parameter int unsigned MEM_AW     = 16,  
  parameter int unsigned MEM_DW     = 32  
)( 
  input  logic              clk,
  input  logic              rst_n,
                            
  input  logic              data_req,
  input  logic              data_we,
  input  logic [3:0]        data_be,
  input  logic [31:0]       data_addr,
  input  logic [MEM_DW-1:0] data_wdata,

  output logic              data_gnt,
  output logic              data_rvalid,
  output logic [MEM_DW-1:0] data_rdata,
  output logic              data_err
);
  
  function automatic logic[3:0] gen_wait(int unsigned wmax);
    logic [3:0]  nwait;
    logic [31:0] randnum;

    randnum = $urandom();
    if (!randnum[31]) nwait = 0;       // 0: 50%
    else nwait = randnum[30:0] & (GNT_WMAX+1);   // 0 to wmax: 0.5/(wmax+1)
    return nwait;
  endfunction
  //
  // simple unified memory system model
  reg   [MEM_DW-1:0] mem[0:2**MEM_AW-1];

  logic              mem_cs;
  logic              mem_we;
  logic        [3:0] mem_be;
  logic [MEM_DW-1:0] mem_din;
  logic [MEM_DW-1:0] mem_dout;
  logic [MEM_AW-1:0] mem_addr;

  logic              gnt_idle, resp_idle;
  logic        [3:0] gnt_cntr, resp_cntr;
  logic        [3:0] gnt_waits, resp_waits;

  logic        [3:0] cmd_rd_ptr_ext, cmd_wr_ptr_ext, fifo_depth;
  logic        [2:0] cmd_rd_ptr, cmd_wr_ptr;
  logic              cmd_fifo_full, cmd_fifo_empty, cmd_avail;
  logic              cmd_fifo_wr, cmd_fifo_rd;
  logic              gnt_no_wait, gnt_wait_done;
  logic              resp_no_wait, resp_wait_done;
  logic              resp_valid;

  typedef struct packed {
    logic              we;
    logic              err;
    logic        [3:0] be;
    logic [MEM_AW-1:0] addr;
    logic [MEM_DW-1:0] wdata;
  } mem_cmd_t;

  mem_cmd_t mem_cmd_fifo[0:7];
  mem_cmd_t cur_wr_cmd, cur_rd_cmd;

  assign cmd_rd_ptr     = cmd_rd_ptr_ext[2:0];
  assign cmd_wr_ptr     = cmd_wr_ptr_ext[2:0];
  assign fifo_depth     = (cmd_wr_ptr_ext - cmd_rd_ptr_ext); 
  assign cmd_fifo_full  = (fifo_depth >= 8);
  assign cmd_fifo_empty = (cmd_wr_ptr_ext == cmd_rd_ptr_ext);
  assign cmd_avail      = cmd_fifo_wr || !cmd_fifo_empty;

  assign cur_wr_cmd.we    = data_we;
  assign cur_wr_cmd.err   = 1'b0;
  assign cur_wr_cmd.be    = data_be;
  assign cur_wr_cmd.addr  = data_addr[MEM_AW+1:2];   // 32-bit addr
  assign cur_wr_cmd.wdata = data_wdata; 

  assign cur_rd_cmd    = mem_cmd_fifo[cmd_rd_ptr];

  assign gnt_no_wait   = data_req && gnt_idle && (gnt_waits == 0) && !cmd_fifo_full;
  assign gnt_wait_done = data_req && !gnt_idle && (gnt_cntr == 1) && !cmd_fifo_full;
  assign cmd_fifo_wr   = gnt_no_wait | gnt_wait_done;

  assign resp_no_wait   = cmd_avail && resp_idle && (resp_waits == 0);
  assign resp_wait_done = cmd_avail && !resp_idle &&  (resp_cntr == 1);

  //
  //  @negedge clk
  //     Grant stage to issue grants and enqueue granted-requests 
  //     dequeue requests to generate memory read/writes
  //
  
  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      data_gnt       <= 1'b0;
      gnt_idle       <= 1'b1;
      gnt_waits      <= 0;
      gnt_cntr       <= 0;
      cmd_wr_ptr_ext <= 0;
      resp_valid     <= 1'b0;
      resp_idle      <= 1'b1;
      resp_waits     <= 0;
      resp_cntr      <= 0;
      cmd_fifo_rd    <= 1'b0;
    end else begin
      if (gnt_no_wait) begin         // zerio-wait case
         gnt_cntr  <= 0;
      end else if (data_req && gnt_idle) begin // starting to wait
         gnt_cntr  <= gnt_waits;
         gnt_idle  <= 1'b0;
      end else if (data_req && !gnt_idle && (gnt_cntr > 1)) begin    // continure waiting 
         gnt_cntr  <= gnt_cntr - 1;
      end else if (gnt_wait_done) begin        // waiting ends, grant
         gnt_cntr  <= 0;
         gnt_idle  <= 1'b1;
      end

      data_gnt <= (gnt_no_wait || gnt_wait_done);
 
      if (cmd_fifo_wr) begin
         mem_cmd_fifo[cmd_wr_ptr] <= cur_wr_cmd;
         cmd_wr_ptr_ext           <= cmd_wr_ptr_ext + 1;
         gnt_waits <= gen_wait (GNT_WMAX);
      end
 
      if (resp_no_wait) begin
         resp_cntr  <= 0;
      end else if (cmd_avail && resp_idle) begin
         resp_cntr  <= resp_waits;
         resp_idle  <= 1'b0;
      end else if (cmd_avail && !resp_idle && (resp_cntr > 1)) begin
         resp_cntr  <= resp_cntr - 1;
      end else if (resp_wait_done) begin
         resp_cntr  <= 0;
         resp_idle  <= 1'b1;
      end

      resp_valid  <= resp_no_wait | resp_wait_done;
      cmd_fifo_rd <= resp_no_wait | resp_wait_done;
    end
  end
  
  // 
  //  @posedge clk
  //    Response stage generate output signals
  //

  assign data_rdata   = mem_dout & {33{data_rvalid}}; 

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      data_rvalid <= 1'b0;
      data_err    <= 1'b0;
      cmd_rd_ptr_ext <= 0;
    end else begin
      data_rvalid <= resp_valid;
      data_err    <= resp_valid & cur_rd_cmd.err;

      if (cmd_fifo_rd) begin
         resp_waits      <= gen_wait(RESP_WMAX);
         cmd_rd_ptr_ext  <= cmd_rd_ptr_ext + 1;
      end
      
    end
  end

  //
  // memory signals (sampled @posedge clk)
  //
  assign mem_cs   = resp_valid & ~cur_rd_cmd.err;
  assign mem_we   = cur_rd_cmd.we;
  assign mem_be   = cur_rd_cmd.be;
  assign mem_din  = cur_rd_cmd.wdata;
  assign mem_addr = cur_rd_cmd.addr;  

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
