module kudu_stats (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        start_stop,
  input  logic        print_req
  );

  `define ISSUER dut.issuer_i

  logic cnt_enable, print_req_q;

  logic       ir0_hazard, ir1_hazard;
  logic       ir0_raw_hazard, ir0_waw_hazard;
  logic       ir1_raw_hazard, ir1_waw_hazard;
  logic [1:0] ir_valid;
  logic       ir0_issued, ir1_issued;
  logic [4:0] reg_wrsv_cause[0:31];
  logic [1:0] ir0_rf_ren, ir1_rf_ren;
  logic       ir0_stall_nohaz, ir1_stall_nohaz, ir1_ooo_rdy;
  logic       ir1_raw_by_ir0;
  logic       ir0_mispredict;
  logic [1:0] branch_mispredict;
  logic [1:0] jal_mispredict;
  logic       pc_set;

  logic [31:0] issue_cnt, cycle_cnt;
  logic [31:0] dual_issue_cnt, single_issue_cnt;
  logic [31:0] ir0_hazard_cnt, ir1_hazard_cnt;

  logic [31:0] ir0_raw_cnt, ir0_waw_cnt;
  logic [31:0] ir1_raw_cnt, ir1_waw_cnt;

  logic [4:0]  ir0_raw_cause, ir1_raw_cause;

  logic [31:0] pc_set_cnt;
  logic [31:0] ir0_branch_mis_cnt, ir1_branch_mis_cnt;
  logic [31:0] ir0_jal_mis_cnt, ir1_jal_mis_cnt;

  logic [31:0] ir0_raw_alu_cnt, ir0_raw_mult_cnt, ir0_raw_ls_cnt;
  logic [31:0] ir1_raw_alu_cnt, ir1_raw_mult_cnt, ir1_raw_ls_cnt;

  logic [31:0] ir0_stall_nohaz_cnt, ir1_stall_nohaz_cnt;
  logic [31:0] ir1_ooo_rdy_cnt, ir1_raw_by_ir0_cnt;

  logic [31:0] ir_valid0_cnt, ir_valid1_cnt, ir_valid2_cnt;
  logic [31:0] single_case_cnt[5];

  // map RTL signals
  assign ir0_hazard = `ISSUER.ir0_hazard_event;
  assign ir1_hazard = `ISSUER.ir1_hazard_event;

  assign ir0_raw_hazard = `ISSUER.ir0_raw_hazard_event;
  assign ir1_raw_hazard = `ISSUER.ir1_raw_hazard_event;
  assign ir0_waw_hazard = `ISSUER.ir0_waw_hazard_event;
  assign ir1_waw_hazard = `ISSUER.ir1_waw_hazard_event;

  assign ir_valid = `ISSUER.ir_valid_i;

  assign ir0_issued = `ISSUER.ir0_issued;
  assign ir1_issued = `ISSUER.ir1_issued;

  assign ir0_raw_cause = `ISSUER.ir0_raw_cause;
  assign ir1_raw_cause = `ISSUER.ir1_raw_cause;

  assign ir0_stall_nohaz = `ISSUER.ir0_stall_nohaz_event;
  assign ir1_stall_nohaz = `ISSUER.ir1_stall_nohaz_event;

  assign ir1_ooo_rdy = `ISSUER.ir1_ooo_rdy_event;
  assign ir1_raw_by_ir0 = `ISSUER.ir1_raw_by_ir0_event;

  assign ir0_mispredict = `ISSUER.branch_mispredict[0];

  assign branch_mispredict = `ISSUER.branch_mispredict_event;
  assign jal_mispredict    = `ISSUER.jal_mispredict_event;
  assign pc_set            = `ISSUER.pc_set_o;

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
      dual_issue_cnt        <= 0;
      single_issue_cnt      <= 0;
      ir0_hazard_cnt        <= 0;
      ir1_hazard_cnt        <= 0;
      ir0_raw_cnt           <= 0;
      ir0_waw_cnt           <= 0;
      ir1_raw_cnt           <= 0;
      ir1_waw_cnt           <= 0;
      ir0_raw_alu_cnt       <= 0;
      ir0_raw_mult_cnt      <= 0;
      ir0_raw_ls_cnt        <= 0;
      ir1_raw_alu_cnt       <= 0;
      ir1_raw_mult_cnt      <= 0;
      ir1_raw_ls_cnt        <= 0;
      ir1_raw_by_ir0_cnt    <= 0;
      ir_valid0_cnt         <= 0;
      ir_valid1_cnt         <= 0;
      ir_valid2_cnt         <= 0;
      ir0_stall_nohaz_cnt   <= 0;
      ir1_stall_nohaz_cnt   <= 0;
      ir1_ooo_rdy_cnt       <= 0;
      single_case_cnt[0]    <= 0;
      single_case_cnt[1]    <= 0;
      single_case_cnt[2]    <= 0;
      single_case_cnt[3]    <= 0;
      single_case_cnt[4]    <= 0;
    end else begin
      if (cnt_enable) begin
        issue_cnt        <= issue_cnt + {31'h0, ir0_issued} + {31'h0, ir1_issued} ;
        cycle_cnt        <= cycle_cnt + 1;
        dual_issue_cnt   <= dual_issue_cnt + ir1_issued; 
        single_issue_cnt <= single_issue_cnt + (ir0_issued & ~ir1_issued); 

        ir0_hazard_cnt   <= ir0_hazard_cnt + ir0_hazard;
        ir1_hazard_cnt   <= ir1_hazard_cnt + ir1_hazard;
        ir0_raw_cnt      <= ir0_raw_cnt + ir0_raw_hazard;
        ir0_waw_cnt      <= ir0_waw_cnt + ir0_waw_hazard;
        ir1_raw_cnt      <= ir1_raw_cnt + ir1_raw_hazard;
        ir1_waw_cnt      <= ir1_waw_cnt + ir1_waw_hazard;

        if (ir0_raw_hazard && (ir0_raw_cause[1] | ir0_raw_cause[2]))
          ir0_raw_alu_cnt <=  ir0_raw_alu_cnt + 1;
        if (ir0_raw_hazard && ir0_raw_cause[3])
          ir0_raw_ls_cnt <=  ir0_raw_ls_cnt + 1;
        if (ir0_raw_hazard && ir0_raw_cause[4])
          ir0_raw_mult_cnt <=  ir0_raw_mult_cnt + 1;

        if (~ir1_raw_by_ir0) begin
          if (ir1_raw_hazard && (ir1_raw_cause[1] | ir1_raw_cause[2]))
            ir1_raw_alu_cnt <=  ir1_raw_alu_cnt + 1;
          if (ir1_raw_hazard && ir1_raw_cause[3])
            ir1_raw_ls_cnt <=  ir1_raw_ls_cnt + 1;
          if (ir1_raw_hazard && ir1_raw_cause[4])
            ir1_raw_mult_cnt <=  ir1_raw_mult_cnt + 1;
        end

        ir0_stall_nohaz_cnt <= ir0_stall_nohaz_cnt + ir0_stall_nohaz; 
        ir1_stall_nohaz_cnt <= ir1_stall_nohaz_cnt + ir1_stall_nohaz; 
        ir1_ooo_rdy_cnt     <= ir1_ooo_rdy_cnt + ir1_ooo_rdy;
        ir1_raw_by_ir0_cnt  <= ir1_raw_by_ir0_cnt + ir1_raw_by_ir0;

        ir_valid0_cnt    <= ir_valid0_cnt + (ir_valid == 2'b00);
        ir_valid1_cnt    <= ir_valid1_cnt + (ir_valid == 2'b01);
        ir_valid2_cnt    <= ir_valid2_cnt + (ir_valid == 2'b11);

			  // ir_valid2 & ~ir0_hazard & (ir1_raw_hazard | shared_resource_not_available | 
        // ir0_branch_misprediction)
        single_case_cnt[0] <= single_case_cnt[0] + ((ir_valid==2'b01) & ir0_issued);
        single_case_cnt[1] <= single_case_cnt[1] + 
                              ((ir_valid==2'b11) & ir0_issued & ir0_mispredict);
        single_case_cnt[2] <= single_case_cnt[2] + 
                              ((ir_valid==2'b11) & ir0_issued & ~ir0_mispredict &
                               ir1_raw_by_ir0);
        single_case_cnt[3] <= single_case_cnt[3] + 
                              ((ir_valid==2'b11) & ir0_issued & ~ir0_mispredict &
                               ~ir1_raw_by_ir0 & ir1_raw_hazard);
        single_case_cnt[4] <= single_case_cnt[4] + ((ir_valid==2'b11) & ir0_issued & ~ir1_issued &
                               ~ir0_mispredict & ~ir1_raw_hazard);
      end
    end
  end

  always_ff  @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_set_cnt         <= 0;
      ir0_branch_mis_cnt <= 0;
      ir1_branch_mis_cnt <= 0;
      ir0_jal_mis_cnt    <= 0;
      ir1_jal_mis_cnt    <= 0;
    end else begin
      if (cnt_enable) begin
        if (pc_set) pc_set_cnt <= pc_set_cnt + 1;

        if (branch_mispredict[0]) ir0_branch_mis_cnt <= ir0_branch_mis_cnt + 1;
        if (branch_mispredict[1]) ir1_branch_mis_cnt <= ir1_branch_mis_cnt + 1;
        if (jal_mispredict[0]) ir0_jal_mis_cnt <= ir0_jal_mis_cnt + 1;
        if (jal_mispredict[1]) ir1_jal_mis_cnt <= ir1_jal_mis_cnt + 1;
      end
    end
  end

  initial begin
    @(posedge rst_ni);

    while (1) begin
      @(posedge clk_i);
      if (print_req & ~print_req_q) begin
        $display("TB>  cycle_cnt\t\t = %7d,  issue_cnt\t\t = %7d", cycle_cnt, issue_cnt);
        $display("TB>  dual_issue_cnt\t = %7d,  single_issue_cnt\t = %7d,  idle_cnt\t\t = %7d",
                  dual_issue_cnt, single_issue_cnt, cycle_cnt - dual_issue_cnt - single_issue_cnt);
        $display("TB>  ir_valid0_cnt\t = %7d,  ir_valid1_cnt\t = %7d,  ir_valid2_cnt\t = %7d",
                       ir_valid0_cnt, ir_valid1_cnt, ir_valid2_cnt);
        $display("TB>  pc_set_cnt\t\t = %7d", pc_set_cnt);
        $display("TB>  ir0_branch_mis_cnt\t = %7d,  ir0_jal_mis_cnt\t = %7d", ir0_branch_mis_cnt, ir0_jal_mis_cnt);
        $display("TB>  ir1_branch_mis_cnt\t = %7d,  ir1_jal_mis_cnt\t = %7d", ir1_branch_mis_cnt, ir1_jal_mis_cnt);
        $display("TB>  x1_irvalid1_cnt\t = %7d,  x1_mispredict0_cnt\t = %7d", 
                       single_case_cnt[0], single_case_cnt[1]);
        $display("TB>  x1_ir1_raw_by0_cnt\t = %7d,  x1_ir1_raw_more_cnt = %7d", 
                       single_case_cnt[2], single_case_cnt[3]);
        $display("TB>  x1_others_cnt\t = %7d", single_case_cnt[4]);

        $display("TB>  ir0_hazard_cnt\t = %7d,  ir0_raw_cnt\t = %7d,  ir0_waw_cnt\t = %7d",
                       ir0_hazard_cnt, ir0_raw_cnt, ir0_waw_cnt);
        $display("TB>  ir0_raw_alu_cnt\t = %7d,  ir0_raw_mult_cnt\t = %7d,  ir0_raw_ls_cnt\t = %7d",
                       ir0_raw_alu_cnt, ir0_raw_mult_cnt, ir0_raw_ls_cnt);
        $display("TB>  ir0_stall_nohaz_cnt = %7d", ir0_stall_nohaz_cnt);

        $display("TB>  ir1_hazard_cnt\t = %7d,  ir1_raw_cnt\t = %7d,  ir1_waw_cnt\t = %7d",
                       ir1_hazard_cnt, ir1_raw_cnt, ir1_waw_cnt);
        $display("TB>  ir1_raw_by_ir0_cnt\t = %7d", ir1_raw_by_ir0_cnt);
        $display("TB>  ir1_raw_alu_cnt\t = %7d,  ir1_raw_mult_cnt\t = %7d,  ir1_raw_ls_cnt\t = %7d",
                       ir1_raw_alu_cnt, ir1_raw_mult_cnt, ir1_raw_ls_cnt);
        $display("TB>  ir1_stall_nohaz_cnt = %7d,  ir1_ooo_rdy_cnt\t = %7d", 
                       ir1_stall_nohaz_cnt, ir1_ooo_rdy_cnt);
      end
    end
  end

endmodule
