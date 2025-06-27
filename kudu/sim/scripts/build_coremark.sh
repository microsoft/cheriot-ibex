#!/bin/bash 
 
set -e 

source ../scripts/common_setup.sh
mkdir -p work
cd work

pwd

POSTFIX="_mcycle"
DEFS="-DPERFORMACE_RUN=1 -DITERATIONS=1 -DCLOCKS_PER_SEC=10000000 -DUSE_MCYCLE_TICK" 

TESTNAME="coremark.cheriot$POSTFIX"
CSRC=../csrc_cheri
SRC=../coremark
S_FILES="$CSRC/startup.S"
OBJ_FILES="startup.o"
C_COMMON="$CSRC/cstart.c $CSRC/util.c"
C_FILES="$C_COMMON $SRC/core_main.c $SRC/core_list_join.c $SRC/core_matrix.c $SRC/core_util.c $SRC/core_state.c $SRC/cheri/core_portme.c $SRC/cheri/ee_printf.c $SRC/cheri/cheri_atest.S"
LD_FILE="../link_coremark.ld"
ELF_OUTPUT=$TESTNAME.elf
BIN_OUTPUT=$TESTNAME.bin
HEX_OUTPUT=$TESTNAME.vhx
 
# run the compile 
BASE_FLAGS="-target riscv32-unknown-unknown -mcpu=cheriot -mabi=cheriot -mxcheri-rvc -Oz -g -nostdlib"
ADDON_CFLAGS="-DNDEBUG -DCOREMARK -I$SRC -I$CSRC -I$SRC/cheri"  

CLANG_FLAGS="$BASE_FLAGS $ADDON_CFLAGS $DEFS" 
 
echo "compile and linking.."
echo $CLANG_FLAGS
$CLANG $BASE_FLAGS -c $S_FILES
$CLANG $CLANG_FLAGS  -DFLAGS_STR="\"$CLANG_FLAGS\"" -T$LD_FILE -o $ELF_OUTPUT $C_FILES $OBJ_FILES
 
$GCC_OBJCOPY -O binary -S $ELF_OUTPUT $BIN_OUTPUT

$BIN2VHX $BIN_OUTPUT > $HEX_OUTPUT
 
echo "Generating disassembled text.."
$LLVM_HOME/llvm-objdump -xdCS --mcpu=cheriot $ELF_OUTPUT > $TESTNAME.dis

echo "Copying binaries to run area.."
cp $HEX_OUTPUT ../../run/bin
cp $ELF_OUTPUT ../../run/bin

