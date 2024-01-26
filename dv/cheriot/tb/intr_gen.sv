// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// random interrupt generator
//
module intr_gen (
  input  logic              clk,
  input  logic              rst_n,

  input  logic [3:0]        INTR_INTVL,  // 0 - no interrupt

  input  logic              intr_en,
  input  logic [2:0]        intr_ack,
  output logic [2:0]        irq
  );


  initial begin
    int nwait;
    logic [31:0] rand32;

    irq = 3'h0;
    @(posedge rst_n);

    // irq state machine
    while (1) begin
      case (irq)
        0: begin       
          rand32 = $urandom();
          if (INTR_INTVL != 0) begin
            nwait = ((rand32 % (2** INTR_INTVL)) + 1) * 10;   // wait at least 10 clk cycles
            repeat (nwait) @(posedge clk);
            // irq = rand32[15:0] % 7 + 1;    // new interrupt
            irq = {2'b00, rand32[0]};         // just do irq_external now. irq_timer causes trouble in sail
          end else begin
            @(posedge clk);
          end
        end
        default: begin    // 
          while (intr_ack == 0) @(posedge clk);
          rand32 = $urandom();
          if (rand32[31])
            irq = 0;
          else 
            // irq = rand32[15:0] % 7 + 1;   // back-to-back interrupts
            irq = {2'b00, rand32[0]};  
          @(posedge clk);
        end
      endcase
    end   
  end

endmodule
