// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// memory model with random gnt/rvalid waits 
//
module mem_obi_if #(
  parameter int unsigned DW         = 32  
)( 
  input  logic          clk,
  input  logic          rst_n,

  input  logic [3:0]    GNT_WMAX,
  input  logic [3:0]    RESP_WMAX,
                        
  input  logic          data_req,
  input  logic          data_we,
  input  logic [3:0]    data_be,
  input  logic          data_req_isr,
  input  logic [31:0]   data_addr,
  input  logic [DW-1:0] data_wdata,

  output logic          data_gnt,
  output logic          data_rvalid,
  output logic [DW-1:0] data_rdata,
  output logic          data_err,

  output logic          mem_cs,
  output logic          mem_we,
  output logic [3:0]    mem_be,
  output logic          mem_req_isr,
  output logic [29:0]   mem_addr32,
  output logic [DW-1:0] mem_wdata,
  input  logic [DW-1:0] mem_rdata,
  input  logic          mem_err
);
  
  function automatic logic[3:0] gen_wait(int unsigned wmax);
    logic [3:0]  nwait;
    logic [31:0] randnum;
    
    if (wmax == 0) return 0;

    randnum = $urandom();
    if (!randnum[31]) nwait = 0;       // 0: 50%
    else nwait = randnum[15:0] % (wmax+1);   // 0 to wmax: 0.5/(wmax+1)
    return nwait;
  endfunction


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
    logic          we;
    logic [3:0]    be;
    logic          req_isr;
    logic [29:0]   addr32;
    logic [DW-1:0] wdata;
  } mem_cmd_t;

  mem_cmd_t mem_cmd_fifo[0:7];
  mem_cmd_t cur_wr_cmd, cur_rd_cmd;

  assign cmd_rd_ptr     = cmd_rd_ptr_ext[2:0];
  assign cmd_wr_ptr     = cmd_wr_ptr_ext[2:0];
  assign fifo_depth     = (cmd_wr_ptr_ext - cmd_rd_ptr_ext); 
  assign cmd_fifo_full  = (fifo_depth >= 8);
  assign cmd_fifo_empty = (cmd_wr_ptr_ext == cmd_rd_ptr_ext);
  assign cmd_avail      = cmd_fifo_wr || !cmd_fifo_empty;

  assign cur_wr_cmd.we      = data_we;
  assign cur_wr_cmd.be      = data_be;
  assign cur_wr_cmd.req_isr = data_req_isr;
  assign cur_wr_cmd.addr32  = data_addr[31:2];   // 32-bit addr
  assign cur_wr_cmd.wdata   = data_wdata; 

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
         gnt_waits   <= gen_wait (GNT_WMAX);
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

  assign data_rdata   = mem_rdata & {33{data_rvalid}}; 

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      data_rvalid <= 1'b0;
      data_err    <= 1'b0;
      cmd_rd_ptr_ext <= 0;
    end else begin
      data_rvalid <= resp_valid;
      data_err    <= resp_valid & mem_err;

      if (cmd_fifo_rd) begin
         resp_waits      <= gen_wait(RESP_WMAX);
         cmd_rd_ptr_ext  <= cmd_rd_ptr_ext + 1;
      end
      
    end
  end

  //
  // memory signals (sampled @posedge clk)
  //
  assign mem_cs      = resp_valid;
  assign mem_we      = cur_rd_cmd.we;
  assign mem_be      = cur_rd_cmd.be;
  assign mem_req_isr = cur_rd_cmd.req_isr;
  assign mem_wdata   = cur_rd_cmd.wdata;
  assign mem_addr32  = cur_rd_cmd.addr32;  

endmodule
