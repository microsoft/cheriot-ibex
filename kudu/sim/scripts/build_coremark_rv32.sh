#!/bin/bash 
 
set -e 

source ../scripts/common_setup.sh
mkdir -p work
cd work

pwd

DEFS="-DPERFORMACE_RUN=1 -DITERATIONS=1 -DCLOCKS_PER_SEC=10000000 -DUSE_MCYCLE_TICK" 
POSTFIX="o3"
#OPT_FLAGS="-O3 -funroll-loops -fmodulo-sched"
OPT_FLAGS="-O3"
# didn't help:  -fschedule-insns
#LD_FILE="../link_coremark_rv32.ld"
LD_FILE="../link_coremark_rv32_large.ld"


TESTNAME="coremark.rv32$POSTFIX"
CSRC=../csrc_rv32_coremark
SRC=../coremark
S_FILES="$CSRC/startup.S $CSRC/vector.S"
OBJ_FILES="startup.o vector.o"
C_COMMON="$CSRC/util.c $CSRC/cstart.c"
C_FILES="$C_COMMON $SRC/core_main.c $SRC/core_list_join.c $SRC/core_matrix.c $SRC/core_util.c $SRC/core_state.c $SRC/riscv32/core_portme.c $SRC/riscv32/ee_printf.c"
ELF_OUTPUT=$TESTNAME.elf
BIN_OUTPUT=$TESTNAME.bin
HEX_OUTPUT=$TESTNAME.vhx

MARCH=rv32imc_zicsr
MABI=ilp32

# run the compile 
BASE_FLAGS="-static -mcmodel=medany -march=$MARCH -mabi=$MABI -nostartfiles -fvisibility=hidden -ffast-math -fno-common -fno-builtin-printf -std=gnu99 -nostdlib -ffreestanding" 

ADDON_CFLAGS="-DNDEBUG -DCOREMARK -I$SRC -I$CSRC -I$SRC/riscv32"  

#RUN_CFLAGS="-DVALIDATION_RUN=1 -DITERATIONS=1 -DCLOCKS_PER_SEC=10000000" 
CFLAGS="$BASE_FLAGS $ADDON_CFLAGS $RUN_CFLAGS $DEFS" 
 
echo "compile and linking.."
echo $CFLAGS
$GCC $BASE_FLAGS -c $S_FILES
#$GCC $CFLAGS  -DFLAGS_STR="\"$CFLAGS\"" -O2 -T$LD_FILE -o $ELF_OUTPUT $C_FILES $OBJ_FILES
$GCC $CFLAGS  -DFLAGS_STR="\"$CFLAGS $OPT_FLAGS\"" $OPT_FLAGS -T$LD_FILE -o $ELF_OUTPUT $C_FILES $OBJ_FILES
 
$GCC_OBJCOPY -O binary -S $ELF_OUTPUT $BIN_OUTPUT

$BIN2VHX $BIN_OUTPUT > $HEX_OUTPUT
 
echo "Generating disassembled text.."
$GCC_OBJDUMP -xdCS $ELF_OUTPUT > $TESTNAME.dis

echo "Copying binaries to run area.."
cp $HEX_OUTPUT ../../run/bin
cp $ELF_OUTPUT ../../run/bin

