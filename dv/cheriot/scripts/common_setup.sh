export LLVM_HOME=/home/shared/hardware/cores/antifortress/lib/CHERI/compiler/bin/
# export GCC_HOME=/home/shared/hardware/common/antifortress/riscv/riscv-gcc-12.2/bin
# export GCC_HOME=/home/shared/hardware/common/antifortress/sifive/riscv64-unknown-elf-gcc-8.2.0-2019.02.0-x86_64-linux-centos6/bin
export GCC_HOME=/usr/local/noncad/riscv-gnu/2023.04.29/bin
export GCC_OBJCOPY=$GCC_HOME/riscv64-unknown-elf-objcopy
export GCC_OBJDUMP=$GCC_HOME/riscv64-unknown-elf-objdump
export GCC=$GCC_HOME/riscv64-unknown-elf-gcc
export CLANG=$LLVM_HOME/clang
export SIM_HOME=/home/kunyanliu/riscdev/ibexc_local/sim
export RUN_BIN=$SIM_HOME/run/bin
export SCRIPTS=$SIM_HOME/scripts
export BIN2HEX=$SCRIPTS/bin2hex.pl

