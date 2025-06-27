OUTPUT_ARCH( "riscv" ) 
/*ENTRY(_start) */ 
 
SECTIONS 
{ 
  . = 0x80000000; 
  .text.vec : {vector.o(.text)} 
  . = 0x80000080; 
  .text.start : {startup.o(.text)} 
  . = ALIGN(0x100); 
  .tohost : { *(.tohost) } 
  . = ALIGN(0x0100); 
  .text : { *(.text) } 
  . = ALIGN(0x0100); 
  . = 0x80008000; 
  .sbss : { *(.sbss) } 
  .rodata : { *(.rodata*) } 
  .data : { *(.data) } 
  .bss : { *(.bss) } 
  _end = .; 
} 
