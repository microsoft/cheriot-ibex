#!/usr/bin/env python3

import sys
import re
from optparse import OptionParser

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
    elif cperms == 0x8 :
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

    top  = (top9 << exp)  + (((addr_val >> (exp+9)) + top_cor)  << (exp+9));
    base = (base9 << exp) + (((addr_val >> (exp+9)) + base_cor) << (exp+9));

    perm = expand_perms(cperms)

    return (tag, perm , obj_type, 0, top, base)        # QQQQ perm coding later. sail doesn't log exp

# 
# trace object (instruction executed)
#
class trace_obj:
    def __init__(self):
        self.valid = 0
        self.cycle = 0
        self.pc = 0
        self.instr = 0     # encoded instruction 
        self.excp = 0
        self.reg_wr = 0           
        self.reg_waddr = 0           
        self.reg_wdata = 0           
        self.reg_wcap = (0, 0, 0, 0, 0, 0)           
        self.mem_wr = 0
        self.mem_rd = 0
        self.mem_addr = 0
        self.mem_size = 0   # 1/2/4/8 bytes: byte/halfword/word/cap
        self.mem_data = 0
    
    def __eq__(self, other):
        if isinstance(other, trace_obj):  # Check if the other object is of the same type
            result = ((self.valid == 1) and (other.valid == 1) and 
                      (self.pc     == other.pc) and 
                      (self.instr  == other.instr) and 
                      (self.excp   == other.excp) and 
                      ((self.excp == 1) or 
                       ((self.reg_wr     == other.reg_wr) and 
                        (self.reg_waddr  == other.reg_waddr) and
                        (self.reg_wdata  == other.reg_wdata) and        
                        (self.reg_wcap   == other.reg_wcap) and        
                        (self.mem_wr     == other.mem_wr) and 
                        (self.mem_rd     == other.mem_rd) and 
                        (self.mem_addr   == other.mem_addr) and 
                        (self.mem_size   == other.mem_size) and 
                        (self.mem_data   == other.mem_data))))
            return result
        return False

    def __str__(self):          # for printing
        pstr = f"trace_obj: {self.valid}, {self.excp}, {self.cycle}, 0x{self.pc:08x}, 0x{self.instr:08x}, " 
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
            print(f"File '{self.filename}' content loaded successfully.")


#
# ibex trace file object
#
class ibex_trace_file(trace_file):
    def find_nxt(self):
        nxt_obj = trace_obj();
        pattern1 = r'^\s*(\d+)\s+(\d+)\s+([0-9A-Fa-f]+)\s+([0-9A-Fa-f]+)\s+(\S+)'  # basic instr
        
        while True:
            if (self.line_ptr >= len(self.lines)):
                break
            matches1 = re.findall(pattern1, self.lines[self.line_ptr])
            if len(matches1) == 0:
                self.line_ptr += 1
            else:
                break
        if len(matches1) != 0:
            nxt_obj.valid = 1
            nxt_obj.cycle = int(matches1[0][1])
            nxt_obj.pc    = int(matches1[0][2], 16)
            nxt_obj.instr = int(matches1[0][3], 16)
            nxt_obj.excp  = 1 if re.search(r'-->', matches1[0][4]) else 0
            
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
                break
            matches1 = re.findall(pattern1, self.lines[self.line_ptr])
            if len(matches1) == 0:
                self.line_ptr += 1
            else:
                break
        #printf("line_ptr =%d\n", self.line_ptr);

        if len(matches1) != 0:
            nxt_obj.valid = 1
            nxt_obj.cycle = int(matches1[0][0])
            nxt_obj.pc    = int(matches1[0][1], 16)
            nxt_obj.instr = int(matches1[0][2], 16)
            
            full_instr = self.lines[self.line_ptr]
            self.line_ptr += 1 

            while True:
                if (self.line_ptr >= len(self.lines)):
                    break
                if re.search(r'^\s*$', self.lines[self.line_ptr]) :  # empty lines
                    self.line_ptr += 1 
                    break
                else:  
                    full_instr += " "
                    full_instr += self.lines[self.line_ptr]
                    self.line_ptr += 1 
                    
            pattern2_0 = r'x(\d+)\s*<-\s*0x([0-9A-Fa-f]+)\s*'  # reg wr
            pattern2_1 = r'\(v:(\d)\s+0x([0-9A-Fa-f]+)-0x([0-9A-Fa-f]+)\s+l:\S+\s+o:0x([0-9A-Fa-f]+)\s+p:(.*?)\)'
            pattern2_2 = r'trapping'
            matches2_0 = re.findall(pattern2_0, full_instr)
            matches2_1 = re.findall(pattern2_1, full_instr)
            matches2_2 = re.findall(pattern2_2, full_instr)
            #print(full_instr)
            #print(matches2_0[0])
            #print(matches2_1[0])

            if len(matches2_0) != 0 and len(matches2_1) != 0 :
                nxt_obj.reg_wr = 1
                nxt_obj.reg_waddr = int(matches2_0[0][0])
                nxt_obj.reg_wdata = int(matches2_0[0][1], 16)
                perms = parse_sail_perms(matches2_1[0][4])
                # printf("perm_str = %s\n", matches2_1[0][4])
                nxt_obj.reg_wcap  = (int(matches2_1[0][0]), perms , int(matches2_1[0][3], 16), 0,
                                     int(matches2_1[0][2], 16), int(matches2_1[0][1], 16))
            
            if len(matches2_2) != 0 :
                nxt_obj.excp = 1

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
            
        return nxt_obj


usage = "Usage: compare_trace.py ibex_trace_file sail_tracefile"
parser = OptionParser(usage=usage)
(options, args) = parser.parse_args()

if (len(args) < 2):
  sys.exit(usage)

ibex_trace_name = args[0]
sail_trace_name = args[1]

trace1 = ibex_trace_file(ibex_trace_name)
trace2 = sail_trace_file(sail_trace_name)

trace1.load()
trace2.load()

cmp_cnt = 0; eq_cnt = 0; neq_cnt = 0

while True:
    obj1 = trace1.find_nxt()
    obj2 = trace2.find_nxt()
    if (obj1.valid == 0) or (obj2.valid == 0):
        break
    if (obj1 == obj2):
        eq_cnt += 1
    else :
        neq_cnt += 1
        print("ibex: ", obj1)
        print("sail: ", obj2)

    cmp_cnt += 1

    del obj1
    del obj2

printf("%d trace objects compared, %d equal, %d not equal\n", cmp_cnt, eq_cnt, neq_cnt)
