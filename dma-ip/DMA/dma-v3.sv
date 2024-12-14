
module dma import cheri_pkg::*; #( 
  parameter int unsigned RegisterCount = 6,
  // check these values from dvp_ibex_core_wrapper
  parameter int unsigned HeapBase      = 32'h2000_0000,
  parameter int unsigned TSMapBase     = 32'h200f_0000, // 4kB default
  parameter int unsigned TSMapTop      = 32'h200f_2000,
  parameter int unsigned TSMapSize     = 2048,           // 32-bit words
  parameter bit          CHERIoTEn     = 1'b1,
  parameter bit          CheriPPLBC    = 1'b1
) (
  input         clk_i,
  input         rstn_i,

  // OBI interface for configurations
  input reg            dma_conf_en_i,
  input reg [31:0]     dma_conf_addr_i,

  input reg [32:0]     dma_conf_wdata_i,
  input reg            dma_conf_we_i,

  // todo: we assume we do not use it yet
  input reg [3:0]      dma_conf_be_i,
  
  // todo: this interface is not tested yet
  output    [32:0]     dma_conf_rdata_o,

  output               dma_conf_ready_o,
  // todo: we assume we do not use it yet
  output               dma_conf_error_o,

  // interrupt interface 
  output reg           dma_completion_intc_o,

  // Deliver to target
  output reg           dma_controller_req_o,
  input                dma_controller_gnt_i,
  
  output reg [31:0]    dma_controller_addr_o,
  // todo: we assume we do not use it yet
  output reg [3:0]     dma_controller_be_o,
  output reg [32:0]    dma_controller_wdata_o,
  output reg           dma_controller_we_o,

  // Read from source 
  input     [32:0]     dma_controller_rdata_i,
  input                dma_controller_rvalid_i,
  // todo: we assume we do not use it yet
  input                dma_controller_error_i,
  
  // this interface is remained to connect to the 
  // temporary safety shadow map
  // todo: but how to differentiate between cpu's tsmap outputs?
  output logic                dma_tsmap_cs_o,
  output logic [15:0]         dma_tsmap_addr_o,
  input  logic [31:0]         dma_tsmap_rdata_i,
  input  logic                tsmap_is_occupied_i,

  input logic                 snooped_tsmap_cs_i,
  input logic [15:0]          snooped_tsmap_addr_i,
  input logic [31:0]          snooped_tsmap_rdata_i
);

// MMAP-able configuration registers
logic [RegisterCount-1:0][31:0] conf_registers, conf_registers_n;
// Capabilities are 66 bits at the hw, with tag bits 
// being replicated at the beginning of each word
logic [65:0] source_capability, source_capability_n;
logic [65:0] target_capability, target_capability_n;

/////////////////////////////////////////////////////////
// Register roles:
//
// Source and target capabilities are 
// in separate registers and indexed at addresses 
// 0, 1 and 2, 3
// 
// For the rest of offset, we save the configurations 
// in the array of registers
//
// conf_registers[0] for DMA transfer length in bytes
// conf_registers[1] for DMA source stride value
// conf_registers[2] for DMA target stride value
// conf_registers[3] for DMA control register: 
//  - includes start('b0), endianness conversion('b1 and 2), reset ('b3)
//  - start bit is meant to be set at the end while programming
// conf_registers[4] for DMA status register
//  - first bit shows the halted status: 0 for idle, and 1 for running
// conf_registers[5] for free command from allocator() to DMA 
//
/////////////////////////////////////////////////////////

// Backpressure registers in case target is not available
logic [31:0] read_data_register, read_data_register_n;
// logic [31:0] write_register, write_register_n;

// states are similar to each other
typedef enum logic [2:0] { IDLE, REQUEST_DATA, WAIT_FOR_DATA, SEND_DATA, ADDRESS_GEN, 
                              RESTART, DMA_HALT_FOR_CHECK } state_t;

state_t state, state_n;
state_t previous_state, previous_state_n;

logic [31:0] read_data_ctr, read_data_ctr_n;

// data is expected to be valid and delivered after single cycle
logic [31:0] read_status_reg, read_status_reg_n;
logic [31:0] source_offset, source_offset_n;
logic [31:0] target_offset, target_offset_n;

// When allocator writes to this interface, 
// we should halt the dma operation, to conduct checks
logic addresses_are_freed;

// restarting dma if there is any request for it
logic restart_dma;
assign restart_dma = conf_registers[3][3];

///////////////////////////////////////////
// Alternative 1: Following is the logic 
// to check the revocation map when free()
// happens at the allocator 
///////////////////////////////////////////

// need to stop the dma when the freed() region 
// turns out to be dma addresses
logic force_stop;
logic first_request_send, first_request_send_n;
logic second_request_send, second_request_send_n;
logic checks_finished, checks_finished_delayed;

// these are interface between the revoker and the dma
// todo: assign these values!
logic [31:0] dma_cap_placeholder;
logic [31:0] tsmap_ptr;
assign tsmap_ptr = (dma_cap_placeholder - HeapBase) >> 3;
assign dma_tsmap_addr_o = tsmap_ptr[15:5];

logic [4:0] bitpos;
assign bitpos = tsmap_ptr[4:0];

// todo: fail if the range is wrong later!
logic correct_range;
assign correct_range = (dma_tsmap_addr_o <= TSMapSize);

logic clear_tag;
assign clear_tag = dma_tsmap_rdata_i[bitpos];

///////////////////////////////////////////
// Alternative 2: Following is the logic 
// to check the snooped tsmap operations 
// for the similarity with dma addresses 
// and the revocation status.
// 
// todo: There are probably some wires that can 
// be joined between alternatives, but 
// we want to keep things separate for the 
// evaluation
///////////////////////////////////////////
logic snooped_addr_similar, snooped_addr_revoked;

logic [31:0] source_address_base, source_address_tsmap;
logic [31:0] target_address_base, target_address_tsmap;

assign source_address_base = (source_capability[31:0] - HeapBase) >> 3;
assign source_address_tsmap = source_address_base[15:5];

assign target_address_base = (target_capability[31:0] - HeapBase) >> 3;
assign target_address_tsmap = target_address_base[15:5];

logic [4:0] source_bitpos, target_bitpos;
assign source_bitpos = source_address_base[4:0];
assign target_bitpos = target_address_base[4:0];

assign snooped_addr_similar = snooped_tsmap_cs_i ? 
                              (source_address_tsmap == snooped_tsmap_addr_i) ||
                              (target_address_tsmap == snooped_tsmap_addr_i)
                              : 0;

assign snooped_addr_revoked = snooped_addr_similar && 
                              (snooped_tsmap_rdata_i[source_bitpos] ||
                               snooped_tsmap_rdata_i[target_bitpos]);

///////////////////////////////////////////
// Alternative 3: Here, we conduct the  
// checks for capabilities at the HW
///////////////////////////////////////////

logic [PERMS_W-1:0] source_perms;
logic [PERMS_W-1:0] target_perms;

assign source_perms = expand_perms(source_capability[63:58]);
assign target_perms = expand_perms(target_capability[63:58]);

logic source_global, source_load;
logic target_global, target_store;

assign source_global = source_perms[PERM_GL];
assign source_load = source_perms[PERM_LD];

assign target_global = target_perms[PERM_GL];
assign target_store = target_perms[PERM_SD];

logic source_unsealed, target_unsealed;

assign source_unsealed = !(source_perms[PERM_US] & source_perms[PERM_SE]);
assign target_unsealed = !(target_perms[PERM_US] & target_perms[PERM_SE]);

logic source_bounded, target_bounded;

logic [TOP_W-1:0] source_top_addr, target_top_addr;
logic [BOT_W-1:0] source_base_addr, target_base_addr;
logic [EXP_W-1:0] source_exp_addr, target_exp_addr;
logic [31:0] source_address_generic, target_address_generic;

assign source_top_addr  = source_capability[41:33];
assign source_base_addr = source_capability[50:42];
assign source_exp_addr  = source_capability[54:51];
assign source_address_generic = source_capability[31:0];

assign target_top_addr  = target_capability[41:33];
assign target_base_addr = target_capability[50:42];
assign target_exp_addr  = target_capability[54:51];
assign target_address_generic = target_capability[31:0];

logic [32:0] source_top_bound, target_top_bound;

logic [3:0] source_cor, target_cor;
logic [1:0] source_top_cor, target_top_cor;
logic [8:0] source_mid_address, target_mid_address;

assign source_mid_address = source_address_generic >> source_exp_addr;
assign target_mid_address = target_address_generic >> target_exp_addr;

assign source_cor = update_temp_fields(source_top_addr, source_base_addr,
                                                  source_mid_address);
assign target_cor = update_temp_fields(target_top_addr, target_base_addr,
                                                  target_mid_address);

assign source_top_cor = source_cor[3:2];
assign target_top_cor = target_cor[3:2];

assign source_top_bound = get_bound33(source_top_addr, source_top_cor, 
                                      source_exp_addr, source_address_generic);

assign target_top_bound = get_bound33(target_top_addr, target_top_cor, 
                                      target_exp_addr, target_address_generic);
logic [31:0] dma_length;
assign dma_length = conf_registers[0];

assign source_bounded = (source_top_bound >= (source_address_generic + dma_length));
assign target_bounded = (target_top_bound >= (target_address_generic + dma_length));

logic source_address_valid, target_address_valid;

// bit 65 and 32 of capability registers are for the valid tags
assign source_address_valid = source_capability[65] & source_global & 
                                source_load & source_unsealed & source_bounded;

assign target_address_valid = target_capability[65] & target_global & 
                                target_store & target_unsealed & target_bounded;

always_ff @( posedge clk_i ) begin : setReset
  if (!rstn_i | restart_dma | force_stop | snooped_addr_revoked) begin
    state <= IDLE;
    previous_state <= IDLE;
    read_data_register <= 0;
    conf_registers <= 0;
    source_capability <= 0;
    target_capability <= 0;
    read_data_ctr <= 0;
    read_status_reg <= 0;
    source_offset <= 0;
    target_offset <= 0;
    first_request_send <= 0;
    second_request_send <= 0;
    addresses_are_freed <= 0;
    checks_finished_delayed <= 0;
  end else if (!addresses_are_freed & conf_registers[5]) begin
    // in order to avoid the repetitive check 
    // in the comb blocks assigning things here
    previous_state <= state;
    state <= DMA_HALT_FOR_CHECK;
    addresses_are_freed <= conf_registers[5];
    checks_finished_delayed <= checks_finished;
  end else begin
    state <= state_n;
    previous_state <= previous_state_n;
    read_data_register <= read_data_register_n;
    conf_registers <= conf_registers_n;
    read_data_ctr <= read_data_ctr_n;
    read_status_reg <= read_status_reg_n;
    source_offset <= source_offset_n;
    target_offset <= target_offset_n;
    first_request_send <= first_request_send_n;
    second_request_send <= second_request_send_n;
    addresses_are_freed <= conf_registers[5];
    checks_finished_delayed <= checks_finished;
    source_capability <= source_capability_n;
    target_capability <= target_capability_n;
  end
end

//////////////////////////////////////
// Step 0: Configurations
//////////////////////////////////////

// always ready to be written and read in IDLE
// assign dma_conf_ready_o = (state == IDLE) || (state == RESTART);
assign dma_conf_ready_o = 1'b1;
assign dma_conf_error_o = 0;

// index of configuration registers decoded
logic [15:0] index;
assign index = dma_conf_addr_i[7:0] >> 2; 

// todo: we need to fix the decoding for read later 
assign read_status_reg_n = (dma_conf_en_i & !dma_conf_we_i) 
                          ? conf_registers[index] 
                          : read_status_reg; 

assign dma_conf_rdata_o = read_status_reg;

// we assume that software can always see the status via reading the registers,
// hence leave the responsibility to overwrite the dma configurations to the programmer.
// offset is 4, because the first two are for the capabilities
generate
  for (genvar i=0; i < RegisterCount-3; i++) begin
    assign conf_registers_n[i] = ((state == IDLE)) 
                                      ? (dma_conf_en_i && dma_conf_we_i && ((i+4) == index)) 
                                      ? dma_conf_wdata_i 
                                      : conf_registers[i]
                                      : conf_registers[i];
  end
endgenerate

// todo: we should be able to write to the control register any time 
// to stop the process?
// todo: then we have to also decouple the byte swap bits 
// to the second register to avoid the problem with control vs conf sync
assign conf_registers_n[3] =  (dma_conf_en_i && dma_conf_we_i && (index == 7)) 
                                      ? dma_conf_wdata_i 
                                      : conf_registers[3];

// this register is written only internally from this hw
assign conf_registers_n[4] = conf_registers[4];

assign conf_registers_n[5] =  (dma_conf_en_i && dma_conf_we_i && (index == 9)) 
                                      ? dma_conf_wdata_i 
                                      : (checks_finished)
                                      ? 0 
                                      : conf_registers[5];

always_comb begin : assignCapabilities
  source_capability_n = source_capability;
  target_capability_n = target_capability;
  
  if (state == IDLE) begin
    // setting a source capability here
    if (dma_conf_en_i && dma_conf_we_i) begin
      if (index == 0) begin
        source_capability_n[32:0] = dma_conf_wdata_i;
      end else if (index == 1) begin
        source_capability_n[65:33] = dma_conf_wdata_i;
      end
      
      // setting a target capability here
      if (index == 2) begin
        target_capability_n[32:0] = dma_conf_wdata_i;
      end else if (index == 3) begin
        target_capability_n[65:33] = dma_conf_wdata_i;
      end
    end
  end

end

///////////////////////////////////////////////////////
// Step 1: Requesting and receiving a data from the source
///////////////////////////////////////////////////////

// todo: we assume we do not use it yet
assign dma_controller_be_o = 'hf;

// increment in terms of 4's
// choose between the source and target addresses to 
// read the data from vs to write the data to
assign dma_controller_addr_o = dma_controller_req_o 
                                  ? dma_controller_we_o 
                                  ? (target_capability[31:0] + target_offset) 
                                  : (source_capability[31:0] + source_offset)  
                                  : 0;

assign read_data_register_n = (state == WAIT_FOR_DATA) & dma_controller_rvalid_i 
                                        ? dma_controller_rdata_i 
                                        : read_data_register;

///////////////////////////////////////////////////////
// Step 2: Sending a data to the target
///////////////////////////////////////////////////////
logic target_data_valid;

assign target_data_valid = dma_controller_req_o & dma_controller_we_o;

logic two_byte_swap, four_byte_swap;

assign two_byte_swap = conf_registers[3][1];
assign four_byte_swap = conf_registers[3][2];

always_comb begin : assignTargetData
  dma_controller_wdata_o = 0;

  if (target_data_valid) begin
    if (two_byte_swap) begin
      dma_controller_wdata_o = {16'b0, read_data_register[7:0], read_data_register[15:8]};
    end else if (four_byte_swap) begin
      dma_controller_wdata_o = {read_data_register[7:0], read_data_register[15:8], 
                                  read_data_register[23:16], read_data_register[31:24]};
    end else begin
      dma_controller_wdata_o = read_data_register;
    end
  end
end

logic start_dma;
assign start_dma = conf_registers[3][0];

// for the start, we implement a simple DMA 
// with single copy operation with one channel
always_comb begin : single_copy_FSM
  state_n = state;
  previous_state_n = previous_state;

  read_data_ctr_n = read_data_ctr;

  source_offset_n = read_data_ctr * (conf_registers[1] + 'b1);  
  target_offset_n = read_data_ctr * (conf_registers[2] + 'b1);  
  
  dma_controller_req_o = 0;
  dma_controller_we_o = 0;

  dma_completion_intc_o = 0;

  force_stop = 1'b0;
  first_request_send_n = first_request_send;
  second_request_send_n = second_request_send;

  dma_tsmap_cs_o = 0;
  dma_cap_placeholder = 0;

  checks_finished = 0;
  
  case (state)
    IDLE: begin
      if (start_dma & source_address_valid & target_address_valid) begin
        state_n = REQUEST_DATA;
      end
    end 
    REQUEST_DATA: begin
      // check whether we already received the expected amount of data
      // unless otherwise, keep receiving a data
      
      // gnt result should be available in the same cycle 
      dma_controller_req_o = 1'b1;

      if (read_data_ctr == dma_length) begin
        read_data_ctr_n = 0;
        state_n = RESTART;
        dma_controller_req_o = 1'b0;

        // interrupt is high only single cycle
        dma_completion_intc_o = 1'b1;
      end else if (checks_finished_delayed) begin
        if (!dma_controller_gnt_i) begin
          checks_finished = 1'b1;
        end else begin
          state_n = WAIT_FOR_DATA;
        end
      end else if (read_data_ctr == (dma_length/2)) begin
        // todo: ideally need to remove this condition later 
        // for free() to happen naturally
        // just wait here, until addresses are freed happens
        dma_controller_req_o = 1'b0;
      end else if (dma_controller_gnt_i) begin
        state_n = WAIT_FOR_DATA;
      end 
      
    end
    WAIT_FOR_DATA: begin
      // we will accept data, once it is valid irrespective 
      // of its ready status.
      // this addtional cycle is to save the data to a register
      // for avoiding back pressure 
      if (dma_controller_rvalid_i) begin
        state_n = SEND_DATA;
      end
    end
    SEND_DATA: begin
      dma_controller_req_o = 1'b1;
      dma_controller_we_o = 1'b1;

      if (dma_controller_gnt_i) begin
        state_n = ADDRESS_GEN;
        read_data_ctr_n = read_data_ctr_n + 'd4;
      end       
    end
    ADDRESS_GEN: begin
      // this additional cycle is for address generation
      // and to remove multiplication from the critical path
      state_n = REQUEST_DATA;
    end
    RESTART: begin
      if (restart_dma) begin
        // the next dma can only launch
        // when the previous one was resetted
        state_n = IDLE;
      end
    end
    DMA_HALT_FOR_CHECK: begin
      if (clear_tag) begin
        force_stop = 1'b1;
        // technically this should be cleared on its own
        // at the first reset/force_stop block above
        state_n = IDLE;
        first_request_send_n = 1'b0;
        second_request_send_n = 1'b0;
      end else if (first_request_send & second_request_send & !clear_tag) begin 
        // if both requests were sent and acknowledged 
        // and no clear tag request still
        // we can switch back to the previous state
        state_n = previous_state;
        previous_state_n = IDLE;
        first_request_send_n = 0;
        second_request_send_n = 0;
        checks_finished = 1'b1;
      end else if (first_request_send & !clear_tag) begin
        dma_tsmap_cs_o = 1'b1;
        dma_cap_placeholder = target_capability[31:0];

        if (!tsmap_is_occupied_i) begin
          second_request_send_n = 1'b1;  
        end
        
      end else if(!first_request_send) begin
        dma_tsmap_cs_o = 1'b1;
        dma_cap_placeholder = source_capability[31:0];

        if (!tsmap_is_occupied_i) begin
          first_request_send_n = 1'b1;
        end
        
      end
      // todo: here make sure to alternate between 
      // the tests for the source and target addr
      // todo: also we do not have any info about the 
      // actual capabilities, need to transfer them as well at the very beginning? 
    end
  endcase
end


endmodule