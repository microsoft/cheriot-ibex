#include <util.h>

#ifdef COREMARK
extern int cheri_atest(int);
extern void core_main(void);
#else
extern int mymain(int, int);
#endif

volatile unsigned int* ramBase;
volatile unsigned int* romBase;
volatile unsigned int* uartReg;

void* globalRoot;


// Ideally we also set the bounds and permissions when deriving from root, but I don't have enough
// information now.
void* from_root(unsigned int addr) {
  return __builtin_cheri_address_set(globalRoot, addr);
}

typedef struct {
  unsigned int addr;
  unsigned int base;
  unsigned int offset;
  unsigned int len;
  unsigned int flags;
} CapReloc;

void populate_caprelocs(CapReloc* caprelocs, unsigned int n)
{
  for (unsigned int i = 0; i < n; ++i) {
    void** capaddr = from_root(caprelocs[i].addr);
    void* cap;
    if (caprelocs[i].flags & 0x80000000U) { // This is a function pointer.
      __asm volatile("auipcc %0, 0": "=C"(cap));
    }
    else
      cap = from_root(0);
    cap = __builtin_cheri_address_set(cap, caprelocs[i].base);
    cap = __builtin_cheri_bounds_set(cap, caprelocs[i].len);
    cap = __builtin_cheri_offset_increment(cap, caprelocs[i].offset);
    *capaddr = cap;
  }
}

// the only reason we need this is to pass argument to main if needed
void cstart(void* gRoot, CapReloc* caprelocs, unsigned int nCaprelocs) {
  globalRoot = gRoot;
  populate_caprelocs(caprelocs, nCaprelocs);

  romBase = from_root(0x00004000U);
  ramBase = from_root(0x80000000U);

  uartReg = from_root(0x83800200U);

#ifdef COREMARK
  cheri_atest(0);
  core_main();
#else
  mymain(0, 0);
#endif

  stop_sim();

  while (1) {;}
}

//void cheri_fault_handler(void) {
//}
