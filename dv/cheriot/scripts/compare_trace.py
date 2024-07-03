#!/usr/bin/env python3

# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import re
import argparse
#from optparse import OptionParser

#
# c-style printf
#
def printf(format, *args):
    sys.stdout.write(format % args)

PERM_GL = 0; PERM_LG = 1; PERM_SD = 2;  PERM_LM = 3;
PERM_SL = 4; PERM_LD = 5; PERM_MC = 6;  PERM_SR = 7;
PERM_EX = 8; PERM_US = 9; PERM_SE = 10; PERM_U0 = 11;
PERM_U1 = 12

#
# convert compressed perm (6-bit integer) to expanded format (13-bit integer)
#

def expand_perms(cperms_in):

    PERM_MC_IMSK = (1<<PERM_LD) | (1<<PERM_MC) | (1<<PERM_SD)
    PERM_LC_IMSK = (1<<PERM_LD) | (1<<PERM_MC)
    PERM_SC_IMSK = (1<<PERM_SD) | (1<<PERM_MC)
    PERM_DD_IMSK = 0
    PERM_EX_IMSK = (1<<PERM_EX) | (1<<PERM_MC) | (1<<PERM_LD)
    PERM_SE_IMSK = 0

    cperms = cperms_in
    perms  = 0
    perms  |= (cperms>>5)        # GL
    cperms &= 0x1f

    if (cperms>>3) == 0x3 :
      perms |= (cperms & 0x1)      << PERM_LG
      perms |= ((cperms & 0x2)>>1) << PERM_LM
      perms |= ((cperms & 0x4)>>2) << PERM_SL
      perms |= PERM_MC_IMSK
    elif (cperms>>2) == 0x5 :
      perms |= (cperms & 0x1)      << PERM_LG
      perms |= ((cperms & 0x2)>>1) << PERM_LM
      perms |= PERM_LC_IMSK
    elif cperms == 0x10 :
      perms |= PERM_SC_IMSK
    elif (cperms>>2) == 0x4 :
      perms |= (cperms & 0x1)      << PERM_SD
      perms |= ((cperms & 0x2)>>1) << PERM_LD
      perms |= PERM_DD_IMSK
    elif (cperms>>3) == 0x1 :
      perms |= (cperms & 0x1)      << PERM_LG
      perms |= ((cperms & 0x2)>>1) << PERM_LM
      perms |= ((cperms & 0x4)>>2) << PERM_SR
      perms |= PERM_EX_IMSK
    elif (cperms>>3) == 0x0 :
      perms |= (cperms & 0x1)      << PERM_US
      perms |= ((cperms & 0x2)>>1) << PERM_SE
      perms |= ((cperms & 0x4)>>2) << PERM_U0
      perms |= PERM_SE_IMSK

    return perms;

#
# parse permissions in sail tracd format to expanded format (13-bit integer)
#

def parse_sail_perms(perm_str):
    perms = 0

    #G RWcgml Xa SU0

    if re.search(r'G', perm_str):    
        perms |= (1 << PERM_GL)
    if re.search(r'R', perm_str):    
        perms |= (1 << PERM_LD)
    if re.search(r'W', perm_str):    
        perms |= (1 << PERM_SD)
    if re.search(r'c', perm_str):    
        perms |= (1 << PERM_MC)
    if re.search(r'g', perm_str):    
        perms |= (1 << PERM_LG)
    if re.search(r'm', perm_str):    
        perms |= (1 << PERM_LM)
    if re.search(r'l', perm_str):    
        perms |= (1 << PERM_SL)
    if re.search(r'X', perm_str):    
        perms |= (1 << PERM_EX)
    if re.search(r'a', perm_str):    
        perms |= (1 << PERM_SR)
    if re.search(r'S', perm_str):    
        perms |= (1 << PERM_SE)
    if re.search(r'U', perm_str):    
        perms |= (1 << PERM_US)
    if re.search(r'0', perm_str):    
        perms |= (1 << PERM_U0)

    return perms;
#
# parse cap in ibex trace format
#

def parse_ibex_cap(cap_val, addr_val):
    tag = cap_val >> 32;
    cperms = (cap_val >> 25) & 0x3f
    obj_type = (cap_val >> 22) & 0x7
    exp = (cap_val >> 18) & 0xf
    exp = 24 if (exp == 15) else exp
    top9 = (cap_val >> 9) & 0x1ff
    base9 = cap_val & 0x1ff
    addrmi9 = (addr_val >> exp) & 0x1ff

    if (top9 < base9) and (addrmi9 < base9) :
        top_cor = 0;
    elif (top9 >= base9) and (addrmi9 >= base9) :
        top_cor = 0;
    elif (top9 < base9) and (addrmi9 >= base9) :
        top_cor = 1;
    else :
        top_cor = -1;

    if addrmi9 < base9 :
      base_cor = -1;
    else :
      base_cor = 0;

    if (exp == 24):
      top  = (top9 << exp);
      base = (base9 << exp);
    else:
      top  = (top9 << exp)  + (((addr_val >> (exp+9)) + top_cor)  << (exp+9));
      base = (base9 << exp) + (((addr_val >> (exp+9)) + base_cor) << (exp+9));

    top  &= 0x1ffffffff    # convert to unsigned
    base &= 0xffffffff

    perm = expand_perms(cperms)

    return (tag, perm , obj_type, 0, top, base)        # QQQQ perm coding later. sail doesn't log exp

# 
# trace object (instruction executed)
#
class trace_obj:
    def __init__(self):
        self.line_num = 0
        self.valid = 0
        self.cycle = 0
        self.pc = 0
        self.instr = 0     # encoded instruction 
        self.is_clc = 0
        self.trap = 0
        self.trap_nxt = 0
        self.trap_pc = 0
        self.intr = 0

        self.reg_wr = 0           
        self.reg_waddr = 0           
        self.reg_wdata = 0           
        self.reg_wcap = (0, 0, 0, 0, 0, 0)           
        self.mem_wr = 0
        self.mem_rd = 0
        self.mem_addr = 0
        self.mem_size = 0   # 1/2/4/8 bytes: byte/halfword/word/cap
        self.mem_data = 0

        self.reg_rd1 = 0    # only for ibex traces
        self.reg_raddr1 = 0
        self.reg_rdata1 = 0
        self.reg_rcap1  = (0, 0, 0, 0, 0, 0)           
        self.reg_rd2 = 0
        self.reg_raddr2 = 0
        self.reg_rdata2 = 0
        self.reg_rcap2  = (0, 0, 0, 0, 0, 0)
        self.uart_wr = 0           
    
    def almost_eq (self, other):
        if isinstance(other, trace_obj):  # Check if the other object is of the same type
            t1 = ((self.valid == 1) and (other.valid == 1) and (self.pc  == other.pc) and 
                 (self.trap   == other.trap))

            # register write check, excluding the wcap tag value (for delayed clc revocation)
            t2 = ((self.instr  == other.instr) and (self.reg_wr == other.reg_wr) and 
                  ((self.reg_wr == 0) or 
                   ((self.reg_wr == 1) and (self.reg_waddr  == other.reg_waddr) and 
                    (self.reg_wdata  == other.reg_wdata) and 
                    (self.reg_wcap[1:5]  == other.reg_wcap[1:5]))))
 
            # no memory access
            t3 = ((self.mem_wr == other.mem_wr) and (self.mem_rd == other.mem_rd) and
                  (self.mem_rd == 0) and (self.mem_rd == 0))

            # memory write good
            t4 = ((self.mem_wr == other.mem_wr) and (self.mem_wr == 1) and 
                  (self.mem_addr == other.mem_addr) and (self.mem_size == other.mem_size) and 
                  (self.mem_data   == other.mem_data))

            # memory read good. 
            # don't need to compare mem data since it goes to registers anyway. also the clcperms
            # makes it hard to compare mem rdata
            t5 = ((self.mem_rd == other.mem_rd) and (self.mem_rd == 1) and 
                  (self.mem_addr == other.mem_addr) and (self.mem_size == other.mem_size))
                   # and (self.mem_data   == other.mem_data))

            # uart write good
            t6 = (self.uart_wr == 1) and (other.uart_wr == 1)  # ignore UART writes

            result = t1 and ((self.trap == 1) or ((self.trap == 0) and t2 and (t3 or t4 or t5 or t6)))
            #print(t1, t2, t3, t4)
            return result
        else: 
            return False

    def __eq__(self, other):
        if self.almost_eq (other) and (self.reg_wcap[0]  == other.reg_wcap[0]):  
            return True
        else:
            return False

    #def only_tag_diff (self. other)       
    #    elseif self.reg_wcap[1:5] == other.reg_wcap
    #    return result

    def __str__(self):          # for printing
        pstr = f"trace_obj: line {self.line_num:6d},"
        pstr += f"{self.valid}, {self.trap}, {self.cycle}, 0x{self.pc:08x}, 0x{self.instr:08x}, " 
        pstr += f"[{self.reg_wr}, {self.reg_waddr}, 0x{self.reg_wdata:X}, "
        pstr += f"({self.reg_wcap[0]}, 0x{self.reg_wcap[1]:x}, 0x{self.reg_wcap[2]:x}, "
        pstr += f"0x{self.reg_wcap[3]:x}, 0x{self.reg_wcap[4]:x}, 0x{self.reg_wcap[5]:x})], "
        pstr += f"[{self.mem_wr}, {self.mem_rd}, 0x{self.mem_addr:x}, 0x{self.mem_data:x}, {self.mem_size}]"
        return pstr
#
# trace file object (generic)
#
class trace_file:
    def __init__(self, filename):
        self.filename   = filename
        self.obj_ptr    = 0;
        self.line_ptr   = 0;
         
    def load(self):
        try:
            self.file = open(self.filename, 'r' )
            print(f"File '{self.filename}' opened successfully.")
        except FileNotFoundError:
            print(f"File '{self.filename}' not found.")
        except Exception as e:
            print(f"An error occurred: {e}")

        content = self.file.read()
        self.lines = content.splitlines()

        if hasattr(self, 'file') and not self.file.closed:
            self.file.close()
            print(f"File '{self.filename}' loaded successfully, {len(self.lines)} lines.")


#
# ibex trace file object
#
class ibex_trace_file(trace_file):
    def find_nxt(self):
        nxt_obj = trace_obj();
        pattern1 = r'^\s*(\d+)\s+(\d+)\s+([0-9A-Fa-f]+)\s+([0-9A-Fa-f]+)\s+(\S+)'  # basic instr
        
        while True:
            if (self.line_ptr >= len(self.lines)):
                return nxt_obj
            matches1 = re.findall(pattern1, self.lines[self.line_ptr])
            if len(matches1) == 0:
                self.line_ptr += 1
            else:
                break

        if len(matches1) != 0:
            nxt_obj.line_num = self.line_ptr

            nxt_obj.valid = 1
            nxt_obj.cycle = int(matches1[0][1])
            nxt_obj.pc    = int(matches1[0][2], 16)
            nxt_obj.instr = int(matches1[0][3], 16)
            nxt_obj.trap  = 1 if re.search(r'-->', matches1[0][4]) else 0
            nxt_obj.intr  = 1 if re.search(r'==>', matches1[0][4]) else 0
            
            mnemonic = matches1[0][4]
            
            pattern2 = r'x(\d+)=0x([0-9A-Fa-f]+)\+0x([0-9A-Fa-f]+)'  # cap reg wr
            matches2 = re.findall(pattern2, self.lines[self.line_ptr])
            pattern3 = r'x(\d+)=0x([0-9A-Fa-f]+)\s*'             # non-cap reg wr
            matches3 = re.findall(pattern3, self.lines[self.line_ptr])
            
            if len(matches2) != 0:
                nxt_obj.reg_wr = 1 if (int(matches2[0][0]) != 0) else 0
                nxt_obj.reg_waddr = int(matches2[0][0])
                nxt_obj.reg_wdata = int(matches2[0][1], 16)
                nxt_obj.reg_wcap  = parse_ibex_cap(int(matches2[0][2], 16), nxt_obj.reg_wdata)
            elif len(matches3) != 0:
                nxt_obj.reg_wr = 1 if (int(matches3[0][0]) != 0) else 0
                nxt_obj.reg_waddr = int(matches3[0][0])
                nxt_obj.reg_wdata = int(matches3[0][1], 16)
                nxt_obj.reg_wcap  = parse_ibex_cap(0, nxt_obj.reg_wdata)
            
            # mem cap
            pattern4 = r'PA:0x([0-9A-Fa-f]+)\s+(load|store):0x([0-9A-Fa-f]+)\+0x([0-9A-Fa-f]+)'
            matches4 = re.findall(pattern4, self.lines[self.line_ptr])
            # mem non-cap
            pattern5 = r'PA:0x([0-9A-Fa-f]+)\s+(load|store):0x([0-9A-Fa-f\?]+)(\s+|$)'
            matches5 = re.findall(pattern5, self.lines[self.line_ptr])

            if len(matches4) != 0:
                nxt_obj.mem_addr = int(matches4[0][0], 16)
                nxt_obj.mem_data = int(matches4[0][3]+(matches4[0][2])[1:],16)
                nxt_obj.mem_size = 8
                if (matches4[0][1]=='load'): 
                    nxt_obj.mem_rd = 1
                else:
                    nxt_obj.mem_wr = 1

            if len(matches5) != 0:
                nxt_obj.mem_addr = int(matches5[0][0], 16)
                mem_data = re.sub(r'\?', '', matches5[0][2])      # for byte/halfword writes
                nxt_obj.mem_data = int(mem_data, 16)

                if (matches5[0][1]=='load'): 
                    nxt_obj.mem_rd = 1
                else:
                    nxt_obj.mem_wr = 1

                if re.search(r'(lb|sb)', mnemonic) : 
                    nxt_obj.mem_size = 1
                elif re.search(r'(lh|sh)', mnemonic) : 
                    nxt_obj.mem_size = 2
                elif re.search(r'(lw|sw)', mnemonic) : 
                    nxt_obj.mem_size = 4

                # for byte/halfword reads to match sail model
                if (nxt_obj.mem_size == 1) and nxt_obj.mem_rd :
                  nxt_obj.mem_data &= 0xff
                elif (nxt_obj.mem_size == 2) and nxt_obj.mem_rd :
                  nxt_obj.mem_data &= 0xffff;

                if (nxt_obj.mem_wr == 1) and (nxt_obj.mem_addr >= 0x10000000) and (nxt_obj.mem_addr < 0x10000100):
                  nxt_obj.uart_wr = 1

            # cap reg rd (cs1 and cs2)
            pattern6 = r'x(\d+):0x([0-9A-Fa-f]+)\+0x([0-9A-Fa-f]+)'  
            matches6 = re.findall(pattern6, self.lines[self.line_ptr])

            nxt_obj.reg_rd1 = 0
            nxt_obj.reg_rd2 = 0

            if len(matches6) >= 1:
                nxt_obj.reg_rd1 = 1
                nxt_obj.reg_raddr1 = int(matches6[0][0])
                nxt_obj.reg_rdata1 = int(matches6[0][1], 16)
                nxt_obj.reg_rcap1  = parse_ibex_cap(int(matches6[0][2], 16), nxt_obj.reg_rdata1)

            if len(matches6) == 2:
                nxt_obj.reg_rd2 = 1
                nxt_obj.reg_raddr2 = int(matches6[1][0])
                nxt_obj.reg_rdata2 = int(matches6[1][1], 16)
                nxt_obj.reg_rcap2  = parse_ibex_cap(int(matches6[1][2], 16), nxt_obj.reg_rdata2)

            self.line_ptr += 1         # get ready for next round
        return nxt_obj


#
# sail trace file object
#
class sail_trace_file(trace_file) :
    def find_nxt(self):
        nxt_obj = trace_obj();
        pattern1 = r'^\s*\[(\d+)\]\s+\[M\]:\s*0x([0-9A-Fa-f]+)\s*\(0x([0-9A-Fa-f]+)\)'  # basic instr

        while True:
            if (self.line_ptr >= len(self.lines)):
               return nxt_obj       # ending search 
            matches1 = re.findall(pattern1, self.lines[self.line_ptr])
            if len(matches1) == 0:
                self.line_ptr += 1
            else:
                break
        #printf("line_ptr =%d\n", self.line_ptr);

        if len(matches1) != 0:
            nxt_obj.line_num = self.line_ptr

            nxt_obj.valid = 1
            nxt_obj.cycle = int(matches1[0][0])
            nxt_obj.pc    = int(matches1[0][1], 16)
            nxt_obj.instr = int(matches1[0][2], 16)
            
            full_instr = self.lines[self.line_ptr]
            self.line_ptr += 1 

            while True:
                if (self.line_ptr >= len(self.lines)):               # end of file
                    break
                if (self.is_rvfi == 0) and re.search(r'^\s*mem\[X', self.lines[self.line_ptr]) :  # another instr
                    self.line_ptr += 1 
                    break
                if re.search(r'^\s*$', self.lines[self.line_ptr]) :  # empty lines
                    self.line_ptr += 1 
                    break
                if (self.is_rvfi == 1) and re.search(r'^\Sending.*response', self.lines[self.line_ptr]) :  # another instr
                    self.line_ptr += 1 
                    break
                full_instr += " "
                full_instr += self.lines[self.line_ptr]
                self.line_ptr += 1 
                    
            pattern2_0 = r'x(\d+)\s*<-\s*0x([0-9A-Fa-f]+)\s*'  # reg wr
            pattern2_1 = r'\(v:(\d)\s+0x([0-9A-Fa-f]+)-0x([0-9A-Fa-f]+)\s+l:\S+\s+o:0x([0-9A-Fa-f]+)\s+p:(.*?)\)'
            pattern2_2 = r'CHERI.*Violation.*PC=0x([0-9A-Fa-f]+)'
            pattern2_3 = r'trapping'
            matches2_0 = re.findall(pattern2_0, full_instr)
            matches2_1 = re.findall(pattern2_1, full_instr)
            matches2_2 = re.findall(pattern2_2, full_instr)
            matches2_3 = re.findall(pattern2_3, full_instr)
            #print(full_instr)
            #print(matches2_0[0])
            #print(matches2_1[0])

            if len(matches2_0) != 0 and len(matches2_1) != 0 :
                nxt_obj.reg_wr = 1
                nxt_obj.reg_waddr = int(matches2_0[0][0])
                nxt_obj.reg_wdata = int(matches2_0[0][1], 16)
                perms = parse_sail_perms(matches2_1[0][4])
                # printf("perm_str = %s\n", matches2_1[0][4])
                # mask off bit 3 of obj_type (implicit by perms)
                nxt_obj.reg_wcap  = (int(matches2_1[0][0]), perms , int(matches2_1[0][3], 16) &0x7, 0,
                                     int(matches2_1[0][2], 16), int(matches2_1[0][1], 16))
            
            if len(matches2_2) != 0 :
                nxt_obj.trap_pc = int(matches2_2[0], 16)
            else :
                nxt_obj.trap_pc = nxt_obj.pc
            
            # QQQ Notewe can have a corner case (not sure how to handle it yet)
            # where mepc == current execution pc (basically trying to trigger a mret fault)
            if len(matches2_3) != 0 and (nxt_obj.trap_pc == nxt_obj.pc):
                nxt_obj.trap = 1
            elif len(matches2_3) != 0 and (nxt_obj.trap_pc != nxt_obj.pc):
                nxt_obj.trap_nxt = 1

            # ?: makes non-grouping
            pattern3 = r'(?:mem|htif)\[.*?0x([0-9A-Fa-f]+)\]\s*(<-|->)\s*0x([0-9A-Fa-f]+)'
            matches3 = re.findall(pattern3, full_instr)
            pattern4 = r'tag\[.*?0x([0-9A-Fa-f]+)\]\s*(<-|->)\s*(\d)'
            matches4 = re.findall(pattern4, full_instr)

            if len(matches3) != 0:
                nxt_obj.mem_wr = 1 if matches3[0][1] == '<-' else 0
                nxt_obj.mem_rd = 1 if matches3[0][1] == '->' else 0
                nxt_obj.mem_addr = int(matches3[0][0], 16)
                nxt_obj.mem_data = int(matches3[0][2], 16)
                nxt_obj.mem_size = len(matches3[0][2]) >> 1

            if len(matches4) != 0:
                tag = int(matches4[0][2])
                #printf ("tag = %d\n", tag)
                nxt_obj.mem_data += (tag<<64)
            
            pattern5 = r'uart\[\S+\]\s*<-'
            matches5 = re.findall(pattern5, full_instr)

            if len(matches5) != 0:
                nxt_obj.uart_wr = 1

        return nxt_obj

    def load(self):             # sail_trace load function
        super().load()
        self.is_rvfi = 0
        pattern0 = r'RVFI'
        i = 0;
        while i < 10 :
            matches0 = re.findall(pattern0, self.lines[i])
            if len(matches0) != 0:
                self.is_rvfi = 1
                print("Sail log is RVFI")
                break
            i += 1

#
# main program body
#

usage = "Usage: compare_trace.py ibex_trace_file sail_tracefile"
#parser = OptionParser(usage=usage)
#(options, args) = parser.parse_args()

# Create ArgumentParser object
parser = argparse.ArgumentParser(description='Command line options')

# Add command line options
parser.add_argument('-k', '--skip_isr', action='store_true', help='Skip ISR in ibex trace')
parser.add_argument('files', nargs='*', help='List of files to process')

# Parse the command line arguments
args = parser.parse_args()


if (len(args.files) == 2):
    print(f'Files specified: {args.files}')
    # Process each file in args.files as needed
else:
    print('No files specified')

if args.skip_isr:
    print('Skipping exception handler in ibex trace')

ibex_trace_name = args.files[0]
sail_trace_name = args.files[1]

ibex_trace = ibex_trace_file(ibex_trace_name)
sail_trace = sail_trace_file(sail_trace_name)

ibex_trace.load()
sail_trace.load()

cmp_cnt = 0; eq_cnt = 0; neq_cnt = 0; revoke_err_cnt = 0; 
ibex_isr_cnt = 0; ibex_dbg_cnt = 0;

pending_revoke_regs = [0] * 32
ibex_in_isr = 0
outstanding_trap = 0

while True:
    if args.skip_isr :          # skipping ISR if specified
        while True:
            ibex_obj = ibex_trace.find_nxt()
            if (ibex_obj.valid == 0):
                break
            if (ibex_obj.trap == 0) and (ibex_obj.intr == 0) and (ibex_in_isr == 0) and (ibex_obj.pc < 0x80040000):
                break
            if (ibex_obj.trap == 1) or  (ibex_obj.intr == 1): 
                ibex_in_isr = 1
                ibex_isr_cnt += 1
            if (ibex_in_isr == 1) and (ibex_obj.instr == 0x30200073):  # mret
                ibex_in_isr = 0
            if (ibex_obj.pc == 0x80040000): 
                ibex_dbg_cnt += 1
    else :  
        ibex_obj = ibex_trace.find_nxt()

    if (outstanding_trap == 0):
        sail_obj = sail_trace.find_nxt()
    else:
        sail_obj = trace_obj()
        sail_obj.valid = 1
        sail_obj.trap  = 1
        sail_obj.trap_nxt = 0
        sail_obj.pc = outstanding_trap_pc

    if (ibex_obj.valid == 0) or (sail_obj.valid == 0):
        break

    # check and update revocation (tag) staus of registers
    if ((pending_revoke_regs[ibex_obj.reg_raddr1] == 1) and (ibex_obj.reg_rd1 == 1) and
        (ibex_obj.reg_rcap1[0] == 1)): 
        revoke_err_cnt += 1; 
        printf("cheriot-ibex: revocation error found for cs1 reg c%d at %x\n", ibex_obj.reg_raddr1, ibex_obj.pc)
    elif ((pending_revoke_regs[ibex_obj.reg_raddr1] == 1) and 
          (ibex_obj.reg_rd1 == 1) and (ibex_obj.reg_rcap1[0] == 0)):
        pending_revoke_regs[ibex_obj.reg_raddr1] = 0;
        eq_cnt += 1
        printf("cheriot-ibex: cap revocation for reg c%d verified at %x\n", ibex_obj.reg_raddr1, ibex_obj.pc)

    if ((pending_revoke_regs[ibex_obj.reg_raddr2] == 1) and (ibex_obj.reg_rd2 == 1) and
        (ibex_obj.reg_rcap2[0] == 1)): 
        revoke_err_cnt += 1; 
        printf("cheriot-ibex: revocation error found for cs2 reg c%d at %x\n", ibex_obj.reg_raddr2, ibex_obj.pc)
    elif ((pending_revoke_regs[ibex_obj.reg_raddr1] == 1) and 
          (ibex_obj.reg_rd2 == 1) and (ibex_obj.reg_rcap2[0] == 0)):
        pending_revoke_regs[ibex_obj.reg_raddr2] = 0;
        eq_cnt += 1
        printf("cheriot-ibex: cap revocation for reg c%d verified at %x\n", ibex_obj.reg_raddr2, ibex_obj.pc)

    if ((pending_revoke_regs[ibex_obj.reg_waddr] == 1) and (ibex_obj.reg_wr == 1)): 
        pending_revoke_regs[ibex_obj.reg_waddr] = 0;
        eq_cnt += 1
        printf("cheriot-ibex: cap revocation for reg c%d cancelled by write at %x\n", ibex_obj.reg_waddr, ibex_obj.pc)
 
    # compare current trace object   
    if (ibex_obj == sail_obj):
        eq_cnt += 1
    elif (ibex_obj.almost_eq(sail_obj) and (ibex_obj.reg_wcap[0] == 1) and 
          (ibex_obj.mem_rd == 1)):           # clc/revocation case
        pending_revoke_regs[ibex_obj.reg_waddr] = 1
        printf("cheriot-ibex: cap revocation for reg c%d started at %x\n", ibex_obj.reg_waddr, ibex_obj.pc)
    else :
        neq_cnt += 1
        print("ibex: ", ibex_obj)
        print("sail: ", sail_obj)

    cmp_cnt += 1

    if (sail_obj.trap_nxt == 1):
        outstanding_trap    = 1
        outstanding_trap_pc = sail_obj.trap_pc
        # printf("--- outstanding trap\n")
    else :
        outstanding_trap    = 0
        outstanding_trap_pc = 0

    del ibex_obj
    del sail_obj


printf("%d trace objects compared, %d equal, %d not equal, %d revocation errors, %d ISRs and %d DBG_REQs found in ibex trace\n", 
        cmp_cnt, eq_cnt, neq_cnt, revoke_err_cnt, ibex_isr_cnt, ibex_dbg_cnt)

ibex_lines_total =  len(ibex_trace.lines)
sail_lines_total =  len(sail_trace.lines)
ibex_lines_left =  len(ibex_trace.lines) - ibex_trace.line_ptr
sail_lines_left =  len(sail_trace.lines) - sail_trace.line_ptr

printf("%d/%d lines left in ibex_trace, %d/%d lines left in sail trace\n", 
        ibex_lines_left, ibex_lines_total, sail_lines_left, sail_lines_total)

revoke_pending = 0;
for i in range(len(pending_revoke_regs)):
    if (pending_revoke_regs[i] != 0):
        revoke_pending = 1;

if (revoke_pending != 0):
    printf("Pending revocations found!\n"); 
    print(pending_revoke_regs)

# ibex usually have more instructions left at the end of simulation since the  RTL simulation
# does not immediate stop after UART request. Worst case is when we have TBRE/stkz transfer still
# in progress, could take > 500 cycles to complete..
if ((neq_cnt == 0) and (revoke_pending == 0) and 
    (not ((ibex_lines_total == 0) and (sail_lines_total == 0))) and 
    ((ibex_lines_left < 1000) and (sail_lines_left == 0))):
    printf("Compare_trace.py: comparison passed :)\n")
else: 
    printf("Compare_trace.py: comparison failed :(\n") 
        
