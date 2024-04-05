extern volatile unsigned int* uartReg;

void send_char(unsigned char);
void prints(char *);
void stop_sim(void);

unsigned int get_tmrval(void);

#define UART_SEND_CHAR(x) (*uartReg = (x))

