#include <util.h>


volatile unsigned int tohost[2];
volatile unsigned int fromhost;

extern volatile unsigned int *uartReg;

void send_char(unsigned char dts) {
    *uartReg = dts;
}

#ifdef USE_MCYCLE_TICK
  unsigned int get_tmrval(void) {
    volatile unsigned int mcycle;
    __asm__ __volatile__("csrr %0, mcycle": "=r" (mcycle));
    return (mcycle);
  }
#else
  static unsigned int mcycle = 0;

  unsigned int get_tmrval(void) {
    mcycle += 100000;         // changed to fixed ticks so we can match sail
    return (mcycle);
  }
#endif

void stop_sim(void) {
  tohost[0] = 0x1;
  tohost[1] = 0x0;
  *uartReg = 0xff;
}

void prints(char *buf) {
  int i;

  i = 0;
  while ((i<100) && (buf[i]!='\0')) {
    send_char(buf[i]);
    i++;
  }
}
