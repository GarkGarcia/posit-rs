//! # TODO
//! * Implement more traits that are implemented for f64
//! * Implement more methods from the f64 API
//! * Implement tests
//! * Add some more documentation
//!
//! ## Missing traits
//! * Display
//! * LowerExp
//! * UpperExp

use crate::internal;
use std::ops::{
    Add, 
    Sub, 
    Mul, 
    Div, 
    Neg, 
    AddAssign, 
    SubAssign, 
    MulAssign, 
    DivAssign
};
use std::cmp::{PartialOrd, Ordering};
use std::fmt::{self, Debug};
use std::iter;

#[derive(Clone, Copy)]
/// 8-bit posit number with zero exponent.
pub struct Posit8(pub(crate) internal::posit8_t);

#[derive(Clone, Copy)]
/// 16-bit posit number with one exponent.
pub struct Posit16(pub(crate)internal::posit16_t);

/// 32-bit posit number with two exponent.
#[derive(Clone, Copy)]
pub struct Posit32(pub(crate)internal::posit32_t);

/// The bit-pattern for infinity on posit8_t
const P8_INFINITY:   u8 = 1 << ( 8 - 1);

/// The bit-pattern for infinity on posit16_t
const P16_INFINITY: u16 = 1 << (16 - 1);

/// The bit-pattern for infinity on posit32_t
const P32_INFINITY: u32 = 1 << (32 - 1);

/// The bit-pattern for 1 on posit8_t
const P8_ONE:   u8 = 1 << ( 8 - 2);

/// The bit-pattern for 1 on posit16_t
const P16_ONE: u16 = 1 << (16 - 2);

/// The bit-pattern for 1 on posit32_t
const P32_ONE: u32 = 1 << (32 - 2);

/// The bit-pattern for -1 on posit8_t
const P8_NEG_ONE:   u8 =  P8_ONE ^ P8_INFINITY;

/// The bit-pattern for -1 on posit16_t
const P16_NEG_ONE: u16 = P16_ONE ^ P16_INFINITY;

/// The bit-pattern for -1 on posit32_t
const P32_NEG_ONE: u32 = P32_ONE ^ P32_INFINITY;

macro_rules! impl_posit {
    ($type:ident, $sqrt:path, $round:path, $mul_add:path, $abs:path, $zero:expr, $inf:expr, $one:expr, $neg_one:expr) => {
        impl $type {
            /// Zero (0).
            pub const ZERO: Self = $zero;

            /// Infinity (±∞).
            pub const INFINITY: Self = $inf;

            /// One (1).
            pub const ONE: Self = $one;

            /// Negative one (-1).
            const NEG_ONE: Self = $neg_one;

            /// Returns the square root of a number.
            ///
            /// Panics if `self < 0`. Returns infinity if `self == ±∞`.
            pub fn sqrt(self) -> Self {
                if self < Self::ZERO {
                    panic!("attempt to compute the square root of a negative number");
                }

                unsafe { self.sqrt_unsafe() }
            }

            /// Returns the same as `Some(self.sqrt())` if `self >= 0`. 
            /// Otherwise returns `None`.
            pub fn sqrt_option(self) -> Option<Self> {
                if self < Self::ZERO {
                    None
                } else {
                    Some(unsafe { self.sqrt_unsafe() })
                }
            }

            /// Returns the same as `self.sqrt()` if `self >= 0`. Otherwise 
            /// returns an unspecified number. Note the return value of this 
            /// method is unspecified if `self < 0`. The caller is expected to 
            /// assert that `self >= 0` before calling this.
            ///
            /// This method _may_ be more performant than `sqrt`.
            pub unsafe fn sqrt_unsafe(self) -> Self {
                Self($sqrt(self.0))
            }

            /// Fused multiply-add. Computes `self * a + b`. Using `mul_add` 
            /// _should_ be more performant than an unfused multiply-add.
            pub fn mul_add(self, a: Self, b: Self) ->  Self {
                Self(unsafe { $mul_add(self.0, a.0, b.0) })
            }

            /// Returns the nearest integer to a number.
            /// Returns infinity if `self == ±∞`.
            pub fn round(self) -> Self {
                Self(unsafe { $round(self.0) })
            }

            /// Returns `true` if this value is zero.
            pub fn is_zero(&self) -> bool {
                self.0.v == 0
            }

            /// Returns `true` if this value is ±∞, and `false` otherwise.
            pub fn is_infinite(&self) -> bool {
                self.0.v == Self::INFINITY.0.v
            }

            /// Returns `true` if this number is not ±∞, and `false` otherwise.
            pub fn is_finite(&self) -> bool {
                ! self.is_infinite()
            }

            /// Computes the absolute value of `self`. Returns ±∞ if the 
            /// number is ±∞.
            pub fn abs(self) -> Self {
                Self(unsafe { $abs(self.0) })
            }

            /// Returns a number that represents the sign of `self`.
            /// * `1` if the number is positive or `0`
            /// * `-1` if the number is negative
            /// * ±∞ if the number is ±∞
            // TODO: Optmize this: maybe we can just look at the sign bit?
            pub fn signum(self) -> Self {
                if self.is_infinite() {
                    self
                } else if self < Self::ZERO {
                    Self::NEG_ONE
                } else {
                    Self::ONE
                }
            }

            /// Returns a number composed of the magnitude of `self` and the 
            /// sign of `sign`.
            /// 
            /// Equal to `sel`f if the sign of `self` and `sign` are the same, 
            /// otherwise equal to `-self`. If `self` is ±∞, then a ±∞ is 
            /// returned.
            // TODO: Optimize this: we don't actully need to compare the signs 
            // in here. This could be more efficient if we were to look at the 
            // first bit of the binary representation of the number.
            pub fn copysign(self, sign: Self) -> Self {
                if self.signum() == sign.signum() {
                    self
                } else {
                    -self
                }
            }
        }

        impl Default for $type {
            fn default() -> Self {
                Self::ZERO
            }
        }
    };
}

macro_rules! impl_from_numeric {
    ($t1:ident, $t2:ident, $f:path) => {
        impl From<$t2> for $t1 {
            fn from(x: $t2) -> Self {
                Self(unsafe { $f(x) })
            }
        }
    };

    ($t1:ident, $t2:ident, $t3:ident, $f:path) => {
        impl From<$t2> for $t1 {
            fn from(x: $t2) -> Self {
                Self(unsafe { $f(x as $t3) })
            }
        }
    };
}

macro_rules! impl_from_posit {
    ($t1:ident, $t2:ident, $f:path) => {
        impl From<$t2> for $t1 {
            fn from(x: $t2) -> Self {
                Self(unsafe { $f(x.0) })
            }
        }
    };
}

macro_rules! impl_into_numeric {
    ($t1:ident, $t2:ident, $f:path) => {
        impl Into<$t2> for $t1 {
            fn into(self) -> $t2 {
                unsafe { $f(self.0) as $t2 }
            }
        }
    };
}

macro_rules! impl_ops {
    ($ops:ident, $ops_f:ident, $ass:ident, $ass_f:ident, $type:ident, $f:path) => {
        impl $ops for $type {
            type Output = Self;

            fn $ops_f(self, other: Self) -> Self {
                $type(unsafe { $f(self.0, other.0) })
            }
        }

        impl<'a> $ops<&'a $type> for $type {
            type Output = $type;

            #[inline]
            fn $ops_f(self, other: &'a Self) -> Self {
                <Self as $ops<$type>>::$ops_f(self, *other)
            }
        }

        impl<'a, 'b> $ops<&'b $type> for &'a $type {
            type Output = $type;

            #[inline]
            fn $ops_f(self, other: &'b $type) -> $type {
                <$type as $ops<&'b $type>>::$ops_f(*self, other)
            }
        }

        impl $ass for $type {
            fn $ass_f(&mut self, other: Self) {
                self.0 = unsafe { $f(self.0, other.0) }
            }
        }

        impl<'a> $ass<&'a $type> for $type {
            fn $ass_f(&mut self, other: &'a Self) {
                <Self as $ass<$type>>::$ass_f(self, *other);
            }
        }
    };
}

macro_rules! impl_add {
    ($t:ident, $f:path) => { 
        impl_ops!(Add, add, AddAssign, add_assign, $t, $f); 
    };
}

macro_rules! impl_sub {
    ($t:ident, $f:path) => { 
        impl_ops!(Sub, sub, SubAssign, sub_assign, $t, $f); 
    };
}

macro_rules! impl_mul {
    ($t:ident, $f:path) => { 
        impl_ops!(Mul, mul, MulAssign, mul_assign, $t, $f); 
    };
}

macro_rules! impl_div {
    ($t:ident, $f:path) => { 
        impl_ops!(Div, div, DivAssign, div_assign, $t, $f); 
    };
}

macro_rules! impl_sum_product {
    ($type:ident) => {
        impl iter::Sum for $type {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ZERO, |a, b| a + b)
            }
        }

        impl iter::Product for $type {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ONE, |a, b| a * b)
            }
        }

        impl<'a> iter::Sum<&'a Self> for $type {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::ZERO, |a, b| a + b)
            }
        }

        impl<'a> iter::Product<&'a Self> for $type {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::from(1u8), |a, b| a * b)
            }
        }
    }
}

macro_rules! impl_neg {
    ($type:ident, $f:path) => {
        impl Neg for $type {
            type Output = Self;

            fn neg(self) -> Self {
                Self(unsafe { $f(self.0) })
            }
        }

        impl<'a> Neg for &'a $type {
            type Output = $type;

            fn neg(self) -> $type {
                <$type as Neg>::neg(*self)
            }
        }
    }
}

macro_rules! impl_eq {
    ($t:ident, $f:path) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                unsafe { $f(self.0, other.0) }
            }
        }

        impl Eq for $t {}
    }
}

macro_rules! impl_ord {
    ($type:ident, $lt:path, $le:path) => {
        impl PartialOrd for $type {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                if self == other {
                    Some(Ordering::Equal)
                } else if unsafe { $lt(self.0, other.0) } {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }

            fn lt(&self, other: &Self) -> bool {
                unsafe { $lt(self.0, other.0) }
            }

            fn le(&self, other: &Self) -> bool {
                unsafe { $le(self.0, other.0) }
            }
        }
    }
}

macro_rules! impl_debug {
    ($type:ident, $fmt:expr) => {
        impl Debug for $type {
            fn fmt(
                &self, 
                f: &mut fmt::Formatter<'_>
            ) -> Result<(), fmt::Error> {
                write!(f, $fmt, self.0.v)
            }
        }
    };
}

// Basic implementation
impl_posit!(
    Posit8, 
    internal::p8_sqrt, 
    internal::p8_roundToInt, 
    internal::p8_mulAdd, 
    internal::p8_abs,
    Posit8(internal::posit8_t { v: 0 }), 
    Posit8(internal::posit8_t { v: P8_INFINITY }),
    Posit8(internal::posit8_t { v: P8_ONE }),
    Posit8(internal::posit8_t { v: P8_NEG_ONE })
);
impl_posit!(
    Posit16, 
    internal::p16_sqrt, 
    internal::p16_roundToInt, 
    internal::p16_mulAdd, 
    internal::p16_abs,
    Posit16(internal::posit16_t { v: 0 }), 
    Posit16(internal::posit16_t { v: P16_INFINITY }),
    Posit16(internal::posit16_t { v: P16_ONE }),
    Posit16(internal::posit16_t { v: P16_NEG_ONE })
);
impl_posit!(
    Posit32, 
    internal::p32_sqrt, 
    internal::p32_roundToInt, 
    internal::p32_mulAdd, 
    internal::p32_abs,
    Posit32(internal::posit32_t { v: 0 }), 
    Posit32(internal::posit32_t { v: P32_INFINITY }),
    Posit32(internal::posit32_t { v: P32_ONE }),
    Posit32(internal::posit32_t { v: P32_NEG_ONE })
);

// Conversions from other numerical types
impl_from_numeric!(Posit8,   i8, i32, internal::i32_to_p8);
impl_from_numeric!(Posit8,  i16, i32, internal::i32_to_p8);
impl_from_numeric!(Posit8,  i32,      internal::i32_to_p8);
impl_from_numeric!(Posit8,  i64,      internal::i64_to_p8);
impl_from_numeric!(Posit8,   u8, u32, internal::ui32_to_p8);
impl_from_numeric!(Posit8,  u16, u32, internal::ui32_to_p8);
impl_from_numeric!(Posit8,  u32,      internal::ui32_to_p8);
impl_from_numeric!(Posit8,  u64,      internal::ui64_to_p8);
impl_from_numeric!(Posit16,  i8, i32, internal::i32_to_p16);
impl_from_numeric!(Posit16, i16, i32, internal::i32_to_p16);
impl_from_numeric!(Posit16, i32,      internal::i32_to_p16);
impl_from_numeric!(Posit16, i64,      internal::i64_to_p16);
impl_from_numeric!(Posit16,  u8, u32, internal::ui32_to_p16);
impl_from_numeric!(Posit16, u16, u32, internal::ui32_to_p16);
impl_from_numeric!(Posit16, u32,      internal::ui32_to_p16);
impl_from_numeric!(Posit16, u64,      internal::ui64_to_p16);
impl_from_numeric!(Posit32,  i8, i32, internal::i32_to_p32);
impl_from_numeric!(Posit32, i16, i32, internal::i32_to_p32);
impl_from_numeric!(Posit32, i32,      internal::i32_to_p32);
impl_from_numeric!(Posit32, i64,      internal::i64_to_p32);
impl_from_numeric!(Posit32,  u8, u32, internal::ui32_to_p32);
impl_from_numeric!(Posit32, u16, u32, internal::ui32_to_p32);
impl_from_numeric!(Posit32, u32,      internal::ui32_to_p32);
impl_from_numeric!(Posit32, u64,      internal::ui64_to_p32);
impl_from_numeric!(Posit8,  f32, f64, internal::convertDoubleToP8);
impl_from_numeric!(Posit16, f32, f64, internal::convertDoubleToP16);
impl_from_numeric!(Posit32, f32, f64, internal::convertDoubleToP32);
impl_from_numeric!(Posit8,  f64,      internal::convertDoubleToP8);
impl_from_numeric!(Posit16, f64,      internal::convertDoubleToP16);
impl_from_numeric!(Posit32, f64,      internal::convertDoubleToP32);

// Convergions from other posit types
impl_from_posit!(Posit8,  Posit16, internal::p16_to_p8);
impl_from_posit!(Posit8,  Posit32, internal::p32_to_p8);
impl_from_posit!(Posit16,  Posit8, internal::p8_to_p16);
impl_from_posit!(Posit16, Posit32, internal::p32_to_p16);
impl_from_posit!(Posit32,  Posit8, internal::p8_to_p32);
impl_from_posit!(Posit32, Posit16, internal::p16_to_p32);

// Conversions to other numerical types
impl_into_numeric!(Posit8,   i32, internal::p8_to_i32);
impl_into_numeric!(Posit8,   i64, internal::p8_to_i64);
impl_into_numeric!(Posit8,  i128, internal::p8_to_i64);
impl_into_numeric!(Posit8,   u32, internal::p8_to_ui32);
impl_into_numeric!(Posit8,   u64, internal::p8_to_ui64);
impl_into_numeric!(Posit8,  u128, internal::p8_to_ui64);
impl_into_numeric!(Posit16,  i32, internal::p16_to_i32);
impl_into_numeric!(Posit16,  i64, internal::p16_to_i64);
impl_into_numeric!(Posit16, i128, internal::p16_to_i64);
impl_into_numeric!(Posit16,  u32, internal::p16_to_ui32);
impl_into_numeric!(Posit16,  u64, internal::p16_to_ui64);
impl_into_numeric!(Posit16, u128, internal::p16_to_ui64);
impl_into_numeric!(Posit32,  i32, internal::p32_to_i32);
impl_into_numeric!(Posit32,  i64, internal::p32_to_i64);
impl_into_numeric!(Posit32, i128, internal::p32_to_i64);
impl_into_numeric!(Posit32,  u32, internal::p32_to_ui32);
impl_into_numeric!(Posit32,  u64, internal::p32_to_ui64);
impl_into_numeric!(Posit32, u128, internal::p32_to_ui64);
impl_into_numeric!(Posit8,   f64, internal::convertP8ToDouble);
impl_into_numeric!(Posit16,  f64, internal::convertP16ToDouble);
impl_into_numeric!(Posit32,  f64, internal::convertP32ToDouble);

// Debuging
impl_debug!(Posit8,  "Posit8({:#010b})");
impl_debug!(Posit16, "Posit16({:#018b})");
impl_debug!(Posit32, "Posit32({:#034b})");

// Arithmetic
impl_add!(Posit8,  internal::p8_add);
impl_add!(Posit16, internal::p16_add);
impl_add!(Posit32, internal::p32_add);
impl_sub!(Posit8,  internal::p8_sub);
impl_sub!(Posit16, internal::p16_sub);
impl_sub!(Posit32, internal::p32_sub);
impl_mul!(Posit8,  internal::p8_mul);
impl_mul!(Posit16, internal::p16_mul);
impl_mul!(Posit32, internal::p32_mul);
impl_div!(Posit8,  internal::p8_div);
impl_div!(Posit16, internal::p16_div);
impl_div!(Posit32, internal::p32_div);
impl_neg!(Posit8,  internal::p8_neg);
impl_neg!(Posit16, internal::p16_neg);
impl_neg!(Posit32, internal::p32_neg);
impl_sum_product!(Posit8);
impl_sum_product!(Posit16);
impl_sum_product!(Posit32);

// Equality
impl_eq!(Posit8,  internal::p8_eq);
impl_eq!(Posit16, internal::p16_eq);
impl_eq!(Posit32, internal::p32_eq);

// Ordering
impl_ord!(Posit8,  internal::p8_lt,  internal::p8_le);
impl_ord!(Posit16, internal::p16_lt, internal::p16_le);
impl_ord!(Posit32, internal::p32_lt, internal::p32_le);

