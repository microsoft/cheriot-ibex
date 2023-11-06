#include <util.h>


volatile unsigned int tohost[2];
volatile unsigned int fromhost;

extern volatile unsigned int *uartReg;

void send_char(unsigned char dts) {
    *uartReg = dts;
}


void stop_sim(void) {
  tohost[0] = 0x1;
  tohost[1] = 0x0;
  *uartReg = 0xff;
}

void prints(char *buf) {
  int i;

  i = 0;
  while ((i<32) && (buf[i]!='\0')) {
    send_char(buf[i]);
    i++;
  }
}
