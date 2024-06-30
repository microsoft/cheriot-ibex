interface core_ibex_dii_intf (
  input clk, input rst_n, input rvfi_valid
);
  logic [31:0] instr_rdata_dii;
  logic        instr_ack;

  clocking cb @(posedge clk);
    output instr_rdata_dii;
    input  instr_ack;
  endclocking

  logic [31:0] instr_in;
  logic [31:0] instr_out;

  bit count_instr_in = 0;

  function void enable_count_instr();
    count_instr_in = 1;
  endfunction

  function void disable_count_instr();
    count_instr_in = 0;
  endfunction

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      instr_in  <= '0;
      instr_out <= '0;
    end else begin
      if (instr_ack && count_instr_in) begin
        instr_in <= instr_in + 32'b1;
      end

      if (rvfi_valid) begin
        instr_out <= instr_out + 32'b1;
      end
    end
  end
endinterface : core_ibex_dii_intf
