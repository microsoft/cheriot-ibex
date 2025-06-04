module ibex_stats (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        start_stop,
  input  logic        print_req
  );

  `define CORE dut.u_ibex_top.u_ibex_core
  `define ID_STAGE dut.u_ibex_top.u_ibex_core.id_stage_i

  logic cnt_enable, print_req_q;

  logic id_instr_done, ir_valid;
  logic stall, stall_ld_hz, stall_multdiv;

  logic [31:0] issue_cnt, cycle_cnt;
  logic [31:0] ir_valid0_cnt, stall_cnt;
  logic [31:0] stall_ld_hz_cnt, stall_multdiv_cnt;

  // map RTL signals
  assign id_instr_done = `ID_STAGE.instr_done;
  assign ir_valid      = `ID_STAGE.instr_valid_i;
  assign stall         = `ID_STAGE.stall_id;
  assign stall_ld_hz   = `ID_STAGE.stall_ld_hz;
  assign stall_multdiv = `ID_STAGE.stall_multdiv;


  always_ff  @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt_enable   <= 1'b0;
      print_req_q  <= 1'b0;  
    end else begin
      if (start_stop) cnt_enable <= ~cnt_enable;
      print_req_q <= print_req;
    end
  end

  always_ff  @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      issue_cnt             <= 0;
      cycle_cnt             <= 0;
      ir_valid0_cnt         <= 0;
      stall_cnt             <= 0;
      stall_ld_hz_cnt       <= 0;
      stall_multdiv_cnt     <= 0;
    end else begin
      if (cnt_enable) begin
        issue_cnt          <= issue_cnt + {31'h0, id_instr_done};
        cycle_cnt          <= cycle_cnt + 1;
        ir_valid0_cnt      <= ir_valid0_cnt + {31'h0, ~ir_valid};
        stall_cnt          <= stall_cnt + {31'h0, stall};
        stall_ld_hz_cnt    <= stall_ld_hz_cnt + {31'h0, stall_ld_hz};
        stall_multdiv_cnt  <= stall_multdiv_cnt + {31'h0, stall_multdiv};
      end
    end
  end

  initial begin
    @(posedge rst_ni);

    while (1) begin
      @(posedge clk_i);
      if (print_req & ~print_req_q) begin
        $display("TB>  cycle_cnt\t\t = %7d,  issue_cnt\t\t = %7d", cycle_cnt, issue_cnt);
        $display("TB>  ir_valid0_cnt\t = %7d,  stall_cnt\t\t = %7d", ir_valid0_cnt, stall_cnt);
        $display("TB>  stall_ld_hz_cnt\t = %7d,  stall_multdiv_cnt\t = %7d", 
                       stall_ld_hz_cnt, stall_multdiv_cnt);
      end
    end
  end

endmodule
