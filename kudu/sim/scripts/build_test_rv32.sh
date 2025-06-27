#!/bin/bash 
 
set -e 

source ../scripts/common_setup.sh
mkdir -p work
cd work
pwd

#export TESTNAME=hello_world
export TESTNAME=$1
export CSRC=../csrc_rv32
export SRC=../$TESTNAME
export C_COMMON="$CSRC/cstart.c $CSRC/util.c"
export S_FILES="$CSRC/startup.S $CSRC/vector.S $SRC/rv32_atest.S"
export C_FILES="$SRC/test_main.c $C_COMMON"
export OBJ_FILES="startup.o vector.o rv32_atest.o"
export C_INC="-I$SRC -I$CSRC"
export LD_FILE=../link_test_rv32.ld

export ELF_OUTPUT=$TESTNAME.elf
export BIN_OUTPUT=$TESTNAME.bin
export HEX_OUTPUT=$TESTNAME.vhx

export MARCH=rv32imc_zicsr
export MABI=ilp32
 
# run the compile 
echo "Start compilation" 
 
BASE_FLAGS="-static -mcmodel=medany -march=$MARCH -mabi=$MABI -nostartfiles -fvisibility=hidden -ffast-math -fno-common -fno-builtin-printf -std=gnu99 -nostdlib -ffreestanding" 

ADDON_CFLAGS="-DNDEBUG -I$SRC -I$CSRC "  
RUN_CFLAGS="" 
CFLAGS="$BASE_FLAGS $ADDON_CFLAGS $RUN_CFLAGS" 
 
echo "compile and linking.."
echo $CFLAGS
$GCC $BASE_FLAGS -c $S_FILES
$GCC $CFLAGS  -DFLAGS_STR="\"$CFLAGS\"" -O2 -T$LD_FILE -o $ELF_OUTPUT $C_FILES $OBJ_FILES

$GCC_OBJCOPY -O binary -S $ELF_OUTPUT $BIN_OUTPUT

$BIN2VHX $BIN_OUTPUT > $HEX_OUTPUT

cp $HEX_OUTPUT ../../run/bin/
cp $ELF_OUTPUT ../../run/bin/


echo "Generating disassembled text.."
$GCC_OBJDUMP -xdCS $ELF_OUTPUT > $TESTNAME.dis

