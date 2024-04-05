#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int cheri_atest(int);

int mymain () {
  int fail_flag, result;

  char *hello_msg = "Hello World!\n";
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

  if (fail_flag == 0) {
    prints(pass_msg);
  }

  return 0;
   
}

