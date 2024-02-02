//`timescale 1ns/1ps

module cap_err_gen import ibex_pkg::*; import cheri_pkg::*; ( 
  input  logic        clk,
  input  logic        rst_n,
  input  logic [2:0]  ERR_RATE,
  input  logic        err_enable,
  output logic        err_active,
  output logic        err_failed 
);

  typedef struct packed {
    logic [7:0]  flag;
    logic        is_cap;
    logic        we;
    logic [1:0]  rv32_type;
    logic [31:0] addr;
    reg_cap_t    cs1_cap;
    logic [31:0] cs1_data;
  } lsu_access_t;

  function automatic lsu_access_t inject_ls_cap_err (lsu_access_t lsu_acc_in, logic[31:0] seed);
    lsu_access_t        lsu_acc_out;
    int                 err_type;
    logic [PERMS_W-1:0] perm_tmp;
    logic [32:0]        top33, base33;
    full_cap_t          fcap;

    lsu_acc_out      = lsu_acc_in;
    lsu_acc_out.flag = 8'h0;

    // let's just inject one single error for now QQQ
    if (lsu_acc_in.is_cap) begin                   // CLC/CSC 
      err_type = seed[15:0] % 5;
      lsu_acc_out.flag = err_type;

      if (err_type == 0) begin                   // TAG error
        lsu_acc_out.cs1_cap.valid = 1'b0;                    
      end else if (err_type == 1) begin          // SEALED error
        lsu_acc_out.cs1_cap.otype = OTYPE_SENTRY;         
      end else if (err_type == 2) begin          
        perm_tmp = expand_perms(lsu_acc_in.cs1_cap.cperms);
        if (~lsu_acc_in.we)                        // LD perm error
          perm_tmp &= ~(1 << PERM_LD);
        else if (seed[31])                       // SD perm error
          perm_tmp &= ~(1 << PERM_SD);
        else                                     // MC perm error
          perm_tmp &= ~(1 << PERM_MC);
        lsu_acc_out.cs1_cap.cperms = compress_perms(perm_tmp, 0);
      end else if (err_type == 3) begin          // address bound error
        fcap = reg2fullcap(lsu_acc_in.cs1_cap, lsu_acc_in.cs1_data);
        lsu_acc_out.flag[6] = 1'b1;              // flag address change
 
        if (seed[31] & (fcap.base32 != 0))       // base vio
          lsu_acc_out.addr = fcap.base32 - 1;        // reduce address by 1
        else if (fcap.top33 != 33'h1_0000_0000)  // top_vio
          lsu_acc_out.addr  = fcap.top33 - seed[2:0];     
        else
          lsu_acc_out.addr  = 32'hffff_ffff;
      end else if (err_type == 4) begin          // alignment error
        lsu_acc_out.flag[6] = 1'b1;              // flag address change
        lsu_acc_out.addr[2:0] = seed[31:24] % 7 + 1'b1;               
      end 
    end else begin                               // RV32 load/store
      err_type = seed[15:0] % 4;
      lsu_acc_out.flag = err_type;

      if (err_type == 0) begin                   // TAG error
        lsu_acc_out.cs1_cap.valid = 1'b0;                    
      end else if (err_type == 1) begin          // SEALED error
        lsu_acc_out.cs1_cap.otype = OTYPE_SENTRY;         
      end else if (err_type == 2) begin          
        perm_tmp = expand_perms(lsu_acc_in.cs1_cap.cperms);
        if (~lsu_acc_in.we)                        // LD perm error
          perm_tmp &= ~(1 << PERM_LD);
        else 
          perm_tmp &= ~(1 << PERM_SD);
        lsu_acc_out.cs1_cap.cperms = compress_perms(perm_tmp, 0);
      end else if (err_type == 3) begin          // address bound error
        fcap = reg2fullcap(lsu_acc_in.cs1_cap, lsu_acc_in.cs1_data);
        lsu_acc_out.flag[6] = 1'b1;              // flag address change
        
        if (seed[31] & (fcap.base32 != 0))           // base vio
          lsu_acc_out.addr = fcap.base32 - 1;            
        else if ((lsu_acc_in.rv32_type == 2'b00) & (fcap.top33 != 33'h1_0000_0000))      // top vio - word
          lsu_acc_out.addr = fcap.top33 - seed[1:0];   
        else if ((lsu_acc_in.rv32_type == 2'b01) & (fcap.top33 != 33'h1_0000_0000))      // half word
          lsu_acc_out.addr = fcap.top33 - seed[0];   
        else if (fcap.top33 != 33'h1_0000_0000)                                        // byte
          lsu_acc_out.addr = fcap.top33;
        else 
          lsu_acc_out.flag[7] = 1'b1;      // let's give up here - have to change both bound and addr..   
      end
    end


    return lsu_acc_out;
  endfunction
    

  logic        cheri_exec_id, cheri_ex_valid;
  logic [35:0] cheri_operator;
  logic        instr_done;
  logic [31:0] pc_id;
  logic        is_rv32_lsu, is_cheri_lsu;
  logic [31:0] rv32_lsu_start_addr;

  logic        cap_err_schd;
  logic [31:0] cap_err_seed;

  logic        pc_in_isr;
  reg_cap_t    rcap_a, rcap_b;
  logic [31:0] rdata_a, rdata_b;

  lsu_access_t lsu_acc_orig, lsu_acc_mod;

  assign cheri_exec_id  = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cheri_exec_id_i;
  assign cheri_ex_valid = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cheri_ex_valid_o;
  assign cheri_operator = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cheri_operator_i;

  assign rv32_lsu_start_addr = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_lsu_addr_i - 
                               {29'h0, dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.addr_incr_req_i, 2'b00};

  assign lsu_acc_orig   = is_rv32_lsu ?  
                          '{8'h0, 1'b0, dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_lsu_we_i,
                            dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_lsu_type_i, 
                            rv32_lsu_start_addr, 
                            rcap_a, rdata_a} :
                          '{8'h0, 1'b1,  cheri_operator[CSTORE_CAP], 2'b00,
                            dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cs1_addr_plusimm,
                            rcap_a, rdata_a};

  assign instr_done     = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_done;
  assign pc_id          = dut.u_ibex_top.u_ibex_core.id_stage_i.pc_id_i;

  assign rcap_a  = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rcap_ng_a;
  assign rcap_b  = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rcap_ng_b;
  assign rdata_a = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rdata_ng_a;
  assign rdata_b = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rdata_ng_b;

  assign is_rv32_lsu  = dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_lsu_req_i;
  assign is_cheri_lsu = cheri_exec_id  & (cheri_operator[CLOAD_CAP] | cheri_operator[CSTORE_CAP]);
  assign pc_in_isr    = (pc_id >= 32'h8000_0000) & (pc_id < 32'h8000_0200);

  assign err_failed = err_active & dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.lsu_req_o &
                      (~dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.lsu_cheri_err_o) & 
                      (~lsu_acc_mod.flag[7]);

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      cap_err_schd <= 1'b0;
      cap_err_seed <= 32'h0;
    end else begin
      if ((is_cheri_lsu | is_rv32_lsu) & instr_done) begin
        cap_err_schd <= err_enable & ((ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-ERR_RATE))==0));
        cap_err_seed <= $urandom();
      end
    end
  end 

  
  initial begin
    err_active = 1'b1;

    @(posedge rst_n);

    while (1) begin
      @(posedge clk);
      #1;
      force dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rcap_a = rcap_a;  // default
      if ((is_cheri_lsu | is_rv32_lsu) & cap_err_schd & ~pc_in_isr) begin 
        lsu_acc_mod  = inject_ls_cap_err(lsu_acc_orig, cap_err_seed);
        force dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rcap_a = lsu_acc_mod.cs1_cap;
        if (is_rv32_lsu && (lsu_acc_mod.flag[7:6] == 2'b01))   // modify address
          force dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_ls_chkaddr = lsu_acc_mod.addr;
        else if (lsu_acc_mod.flag[7:6] == 2'b01)
          force dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cheri_ls_chkaddr = lsu_acc_mod.addr;
        err_active = 1'b1;
      end else begin
        release dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rf_rcap_a;
        release dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.rv32_ls_chkaddr;
        release dut.u_ibex_top.u_ibex_core.g_cheri_ex.u_cheri_ex.cheri_ls_chkaddr;
        err_active = 1'b0;
      end
    end
  end
endmodule
