use crate::internal;
use crate::posit::{Posit8, Posit16, Posit32};
use std::fmt::{self, Debug};

#[derive(Clone, Copy)]
pub struct Quire8(internal::quire8_t);

#[derive(Clone, Copy)]
pub struct Quire16(internal::quire16_t);

#[derive(Clone, Copy)]
pub struct Quire32(internal::quire32_t);

macro_rules! impl_quire {
    ($type:ident, $posit:ident, $fdp_add:path, $fdp_sub:path, $clear:expr) => {
        impl $type {
            /// The zero quire.
            pub const CLEAR: Self = Self($clear);

            /// Sets `self` to zero.
            pub fn clear(&mut self) {
                self.0 = $clear;
            }

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
    }
}

macro_rules! impl_into_posit {
    ($type:ident, $posit:ident, $f:path) => {
        impl Into<$posit> for $type {
            fn into(self) -> $posit {
                $posit(unsafe { $f(self.0) })
            }
        }
    }
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
    fn fmt(
        &self, 
        f: &mut fmt::Formatter<'_>
    ) -> Result <(), fmt::Error> {
        write!(f, "Quire8({:#034b})", self.0.v)
    }
}

impl Debug for Quire16 {
    fn fmt(
        &self, 
        f: &mut fmt::Formatter<'_>
    ) -> Result <(), fmt::Error> {
        write!(f, "Quire16({:#066b}, {:#066b})", self.0.v[0], self.0.v[1])
    }
}

impl Debug for Quire32 {
    fn fmt(
        &self, 
        f: &mut fmt::Formatter<'_>
    ) -> Result <(), fmt::Error> {
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

