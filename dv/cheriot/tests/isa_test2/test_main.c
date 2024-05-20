#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int cheri_atest(int);

unsigned int temp_array[16];
volatile unsigned char *ptr1;

int mymain () {
  int fail_flag, result;
  int i, j;
  unsigned int tint1, tint2;
  unsigned short ts1, ts2;

  char *hello_msg = "Running ISA test 2!\n";
  char *unaligned_msg = "Testing unaligned load/stores..\n";
  char *pass_msg = "\nTest passed :-)\n";
  char *fail_msg = "\nTest failed :-(((((\n";

  prints(hello_msg);

  fail_flag = 0;

  result = cheri_atest(0);
  if (result != 0) {
    prints(fail_msg);
    fail_flag += result;
    return -1;
  }

  // initialze the array to get rid of the IbexDataRPayloadX assertions
  for (i=0; i<16;i++) temp_array[i] = 0;

  // test unaligned word accesses
  prints(unaligned_msg);

  for (i=0; i< 20; i++) {
    tint1 = 0xdeadbeef;
    ptr1 = (unsigned char *) &temp_array;
    for (j=0; j < 32; j++) {
      ptr1++;
      *((volatile unsigned int *) ptr1) = tint1;
      tint2 = *((volatile unsigned int *) ptr1);
      if (tint1 != tint2) {fail_flag++;}
      tint1 += 0x12345678;
    }
  }

  for (i=0; i< 20; i++) {
    ts1 = 0xabcd;
    ptr1 = (unsigned char *) &temp_array;
    for (j=0; j < 32; j++) {
      ptr1++;
      *((volatile unsigned short *) ptr1) = ts1;
      ts2 = *((volatile unsigned short *) ptr1);
      if (ts1 != ts2) {fail_flag++;}
      ts1 += 0x1213;
    }
  }

  if (fail_flag == 0) {
    prints(pass_msg);
  }

  return 0;
   
}

