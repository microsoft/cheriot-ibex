#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))


int mymain () {
  char *hello_msg = "Hello world!\n";

  prints(hello_msg);
}

