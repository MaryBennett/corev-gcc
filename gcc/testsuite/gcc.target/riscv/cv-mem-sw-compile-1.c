/* { dg-do compile } */
/* { dg-require-effective-target cv_mem } */
/* { dg-options "-march=rv32i_xcvmem -mabi=ilp32 -fno-unroll-loops" } */
/* { dg-skip-if "" { *-*-* } { "-O0" "-Og" } } */

/*
 * Test for post-inc register-immediate saves.
 */

int
fooSIsigned (signed int* array_int)
{
  int int_sum = 1;

  for (int i = 0; i < 200; i++)
    array_int [i] += int_sum;

  return int_sum;
}

int
fooSIunsigned (unsigned int* array_uint)
{
  int uns_int_sum = 1;

  for (int i = 0; i < 200; i++)
    array_uint [i] += uns_int_sum;

  return uns_int_sum;
}

/* { dg-final { scan-assembler-times "cv\\.sw\t\(\?\:t\[0-6\]\|a\[0-7\]\|s\[1-11\]\),\\(\(\?\:t\[0-6\]\|a\[0-7\]\|s\[1-11\]\)\\),4" 2 } } */
