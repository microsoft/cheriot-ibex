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
  output logic [2:0]        irq_o
  );

  logic [2:0]  irq;

  //assign irq_o = intr_en & irq;   // hard gate irq output (otherwise nwait cause delay)
  assign irq_o = irq;   

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
          if (intr_en && (INTR_INTVL != 0)) begin
            nwait = ((rand32 % (2** INTR_INTVL)) + 1) * 10;   // wait at least 10 clk cycles
            repeat (nwait) @(posedge clk);
            if (intr_en) begin                  // test intr_en again 
              // irq = rand32[15:0] % 7 + 1;    // new interrupt
              irq = {2'b00, rand32[0]};         // just do irq_external now. irq_timer causes trouble in sail
              //$display ("going irq=1 @%t", $time);
            end
          end else begin
            @(posedge clk);
          end
        end
        default: begin    // 
          while (intr_ack == 0) @(posedge clk);
          rand32 = $urandom();
          if (rand32[31] | ~intr_en) begin
            irq = 0;
            //$display ("going irq=0 @%t", $time);
          end else begin
            // irq = rand32[15:0] % 7 + 1;   // back-to-back interrupts
            irq = {2'b00, rand32[0]};  
          end
          @(posedge clk);
        end
      endcase
    end   
  end

endmodule
