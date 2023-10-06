#include <stdio.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

#define L 16

extern void test_map_simple_u64(uint64_t *p);
extern void test_map_optimized_u64(uint64_t *p);

void init(uint64_t *a, uint64_t e)
{
  for(size_t i=0; i<L; i++)
  { a[i] = e; }
}

void print(char *s, uint64_t *a)
{
  printf("%s", s);
  for(size_t i=0; i<L-1; i++)
  { printf("%" PRId64 ", ", a[i]); }
  printf("%ld\n", a[L-1]);
}

int main(void)
{
  uint64_t a[L], b[L], c[L];

  init(a, 1);
  init(b, 2);
  init(c, 3);

  printf("State before map (+1) on 'a' and 'b':\n");
  print(" a: ", a);
  print(" b: ", b);

  test_map_simple_u64(a);
    assert(memcmp(a, b, sizeof(uint64_t) * L) == 0);

  test_map_optimized_u64(b);
    assert(memcmp(b, c, sizeof(uint64_t) * L) == 0);

  printf("\nState after map (+1) on 'a' and 'b':\n");
  print(" a: ", a);
  print(" b: ", b);

  return 0;
}
