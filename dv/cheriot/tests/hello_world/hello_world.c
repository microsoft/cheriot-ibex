#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int cheri_atest(int);

int mymain () {
  char *hello_msg = "Hello world!\n";

  prints(hello_msg);

  cheri_atest(0);
}

