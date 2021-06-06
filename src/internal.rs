#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

/// The bit-pattern for NaR on posit8_t
pub const P8_NAR: u8 = 1 << (8 - 1);

/// The bit-pattern for NaR on posit16_t
pub const P16_NAR: u16 = 1 << (16 - 1);

/// The bit-pattern for NaR on posit32_t
pub const P32_NAR: u32 = 1 << (32 - 1);

/// The bit-pattern for 1 on posit8_t
pub const P8_ONE: u8 = 1 << (8 - 2);

/// The bit-pattern for 1 on posit16_t
pub const P16_ONE: u16 = 1 << (16 - 2);

/// The bit-pattern for 1 on posit32_t
pub const P32_ONE: u32 = 1 << (32 - 2);

/// The bit-pattern for -1 on posit8_t
pub const P8_NEG_ONE: u8 = P8_ONE ^ P8_NAR;

/// The bit-pattern for -1 on posit16_t
pub const P16_NEG_ONE: u16 = P16_ONE ^ P16_NAR;

/// The bit-pattern for -1 on posit32_t
pub const P32_NEG_ONE: u32 = P32_ONE ^ P32_NAR;

