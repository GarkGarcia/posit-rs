#include "SoftPosit/source/include/softposit.h"

// TODO: Extract the functions below to a separate source file
// TODO: Use the absP macros when they are fixed

posit8_t p8_neg(posit8_t a) {
  return negP8(a);
}

posit16_t p16_neg(posit16_t a) {
  return negP16(a);
}

posit32_t p32_neg(posit32_t a) {
  return negP32(a);
}

posit8_t p8_abs(posit8_t a) {
  union ui8_p8 uA;
  uA.p = a;
  int const mask = uA.ui >> 7;
  uA.ui = ((uA.ui + mask) ^ mask)&0xFF;
  uA.p;
}

posit16_t p16_abs(posit16_t a) {
  union ui16_p16 uA;
  uA.p = a;
  int const mask = uA.ui >> 15;
  uA.ui = ((uA.ui + mask) ^ mask)&0xFFFF;
  uA.p;
}

posit32_t p32_abs(posit32_t a) {
  union ui32_p32 uA;
  uA.p = a;
  int const mask = uA.ui >> 31;
  uA.ui = ((uA.ui + mask) ^ mask)&0xFFFFFFFF;
  uA.p;
}

