//! Bindings for the quire types.
//!
//! ## TODO
//! * Investigate the possibility of making the dot_product_ methods take a
//!   mutable reference to self
//! * Update the examples: instead of printing the results we should check if
//!   the results match the expected ones with assert_eq!
//!
use crate::internal;
use crate::posit::{Posit16, Posit32, Posit8};
use std::fmt::{self, Debug};

/// 8-bit posit quire.
///
/// ```
/// use posit_rs::{Posit8, Quire8};
///
/// fn main() {
///     // Convert doubles to posits
///     let a = Posit8::from(1.0278803125f64);
///     let b = Posit8::from(0.987060546875f64);
///     let c = Posit8::from(0.4998779296875f64);
///     let d = Posit8::from(0.8797607421875f64);
///
///     // Set quire to 0
///     let mut q = Quire8::CLEAR;
///
///     // Accumulate products without roundings
///     q = q.dot_product_add(a, b);
///     q = q.dot_product_add(c, d);
///
///     // Convert back to posit
///     let p: Posit8 = q.into();
///
///     // Check the answer
///     println!("{}", f64::from(p));
/// }
/// ```
#[derive(Clone, Copy)]
pub struct Quire8(internal::quire8_t);

/// 16-bit posit quire.
///
/// ```
/// use posit_rs::{Posit16, Quire16};
///
/// fn main() {
///     // Convert doubles to posits
///     let a = Posit16::from(1.02781603125f64);
///     let b = Posit16::from(0.987060546875f64);
///     let c = Posit16::from(0.4998779296875f64);
///     let d = Posit16::from(0.8797607421875f64);
///
///     // Set quire to 0
///     let mut q = Quire16::CLEAR;
///
///     // Accumulate products without roundings
///     q = q.dot_product_add(a, b);
///     q = q.dot_product_add(c, d);
///
///     // Convert back to posit
///     let p: Posit16 = q.into();
///
///     // Check the answer
///     println!("{}", f64::from(p));
/// }
/// ```
#[derive(Clone, Copy)]
pub struct Quire16(internal::quire16_t);

/// 32-bit posit quire.
///
/// ```
/// use posit_rs::{Posit32, Quire32};
///
/// fn main() {
///     // Convert doubles to posits
///     let a = Posit32::from(1.02783203125f64);
///     let b = Posit32::from(0.987060546875f64);
///     let c = Posit32::from(0.4998779296875f64);
///     let d = Posit32::from(0.8797607421875f64);
///
///     // Set quire to 0
///     let mut q = Quire32::CLEAR;
///
///     // Accumulate products without roundings
///     q = q.dot_product_add(a, b);
///     q = q.dot_product_add(c, d);
///
///     // Convert back to posit
///     let p: Posit32 = q.into();
///
///     // Check the answer
///     println!("{}", f64::from(p));
/// }
/// ```
#[derive(Clone, Copy)]
pub struct Quire32(internal::quire32_t);

macro_rules! impl_quire {
  ($type:ident, $posit:ident, $fdp_add:path, $fdp_sub:path, $clear:expr) => {
    impl $type {
      /// The zero quire.
      pub const CLEAR: Self = Self($clear);

      /// Fused dot product-add. Computes `self + a * b`.
      pub fn dot_product_add(self, a: $posit, b: $posit) -> Self {
          Self(unsafe { $fdp_add(self.0, a.0, b.0) })
      }

      /// Fused dot product-subtract. Computes `self - a * b`.
      pub fn dot_product_sub(self, a: $posit, b: $posit) -> Self {
          Self(unsafe { $fdp_sub(self.0, a.0, b.0) })
      }
    }

    impl Default for $type {
      fn default() -> Self {
        Self::CLEAR
      }
    }
  };
}

macro_rules! impl_into_posit {
  ($type:ident, $posit:ident, $f:path) => {
    impl From<$type> for $posit {
      fn from(a: $type) -> $posit {
        $posit(unsafe { $f(a.0) })
      }
    }
  };
}

impl_quire!(
  Quire8,
  Posit8,
  internal::q8_fdp_add,
  internal::q8_fdp_sub,
  internal::quire8_t { v: 0 }
);
impl_quire!(
  Quire16,
  Posit16,
  internal::q16_fdp_add,
  internal::q16_fdp_sub,
  internal::quire16_t { v: [0; 2] }
);
impl_quire!(
  Quire32,
  Posit32,
  internal::q32_fdp_add,
  internal::q32_fdp_sub,
  internal::quire32_t { v: [0; 8] }
);

impl_into_posit!(Quire8, Posit8, internal::q8_to_p8);
impl_into_posit!(Quire16, Posit16, internal::q16_to_p16);
impl_into_posit!(Quire32, Posit32, internal::q32_to_p32);

impl Debug for Quire8 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "Quire8({:#034b})", self.0.v)
  }
}

impl Debug for Quire16 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "Quire16({:#066b}, {:#066b})", self.0.v[0], self.0.v[1])
  }
}

impl Debug for Quire32 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(
      f,
      "Quire32({:#066b}, {:#066b}, {:#066b}, {:#066b}, {:#066b}, {:#066b}, {:#066b}, {:#066b})",
      self.0.v[0],
      self.0.v[1],
      self.0.v[2],
      self.0.v[3],
      self.0.v[4],
      self.0.v[5],
      self.0.v[6],
      self.0.v[7]
    )
  }
}
