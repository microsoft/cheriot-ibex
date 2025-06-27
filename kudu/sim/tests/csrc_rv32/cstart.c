void stop_sim(void);

#ifdef COREMARK
extern void core_main(void);
#else
extern int mymain(int, int);
#endif

volatile unsigned int* uartReg;
extern 

// the only reason we need this is to pass argument to main if needed
void cstart(void) {
  uartReg = (unsigned int *) (0x83800200U);

#ifdef COREMARK
  core_main();
#else
  mymain(0, 0);
#endif

  stop_sim();

  while (1) {;}
}

