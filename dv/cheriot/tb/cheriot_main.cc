// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vtb_cheriot_top.h"
#include "Vtb_cheriot_top___024root.h"

#define MAX_SIM_TIME 2000000000        // 100M cycles
// #define VCD_TRACE
vluint64_t sim_time = 0;

int main(int argc, char** argv, char** env) {
    unsigned char exit_flag, exit_cnt, first_cycle;
    unsigned int nxt_instr;

    std::ifstream file(argv[1]); // Replace with your file path
    std::string line;

    if (!file) {
        std::cerr << "Failed to open the file." << std::endl;
        return 1;
    }

    Verilated::commandArgs(argc, argv);
    Vtb_cheriot_top *dut = new Vtb_cheriot_top;

    Verilated::traceEverOn(true);
    VerilatedVcdC *m_trace = new VerilatedVcdC;
#ifdef VCD_TRACE
    dut->trace(m_trace, 10);
    m_trace->open("waveform.vcd");
#endif
    uint64_t sim_time = 0;

    dut->clk_i = 0;
    dut->rstn_i = 1;
    dut->dii_insn_i = 0x1;

    first_cycle = 1;
    exit_flag   = 0;
    exit_cnt    = 0;

    std::getline(file, line);
    std::istringstream iss(line);
    iss >> std::hex >> nxt_instr;

    while (sim_time < MAX_SIM_TIME && (exit_cnt < 10)) {
    // while (!Verilated::gotFinish()) {
        dut->clk_i ^= 1;

#ifdef VCD_TRACE
        m_trace->dump(sim_time);
#endif
        if ((sim_time > 12) && (!dut->clk_i)) {      // falling edge logic
            if (first_cycle || dut->dii_ack_o) {
                dut->dii_insn_i = nxt_instr;
                first_cycle = 0;
                // printf("@%d: nxt_instr = %08x\n", sim_time, nxt_instr);
                if (dut->dii_ack_o) {
                    if (std::getline(file, line)) {
                        std::istringstream iss(line);
                        iss >> std::hex >> nxt_instr;
                    } else {
                        exit_flag = 1;
                        nxt_instr = 0x1;
                    } 
                }
            }

            if (exit_flag) {exit_cnt++;}
        }   // falling edge

        dut->eval();
        sim_time++;
        if (sim_time == 10) { dut->rstn_i = 0;} 
        else if (sim_time == 20) { dut->rstn_i = 1; }
    }

#ifdef VCD_TRACE
    m_trace->close();
#endif
    delete dut;
    file.close();

    printf ("cheriot_main: simulation completed\n");
    exit(0);
}
