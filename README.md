# posit_rs

Rust bindings for the [SoftPosit](https://gitlab.com/cerlane/SoftPosit)
C library.

Posit numbers are an alternative to
[floating-point numbers](https://en.wikipedia.org/wiki/Floating_point),
they are a standard for representing
[real numbers](https://en.wikipedia.org/wiki/Real_number) in a computer.
More specifically, posit numbers are a way to represent
[Stone-Cech's compactification](
https://en.wikipedia.org/wiki/Stone%E2%80%93%C4%8Cech_compactification)
of the real number line. In other words, a posit number represents either a
real number or NaR (_not a real_, which stands for ±∞). The main
differences between posit numbers and floating-point numbers are:

* Posit arithmetic is generally more precise.
* There is a single infinite posit value (NaR or ±∞) as opposed to two
  distinct infinite floating-point values (+∞ and −∞).
* There is no NaN posit value, and there is a single bit-pattern
  representation for NaR as opposed to multiple bit-pattern
  representations of NaN. This implies NaR = NaR always hold.
* There is single null posit value (±0) as opposed to two distinct null
  floating-point values (+0 and −0).

For more information on posit numbers and on the specifics of the
representation please refer to
[_Beating Floating Point at it's Own Game_](
http://www.johngustafson.net/pdfs/BeatingFloatingPoint.pdf) or
[_Beyond Floating Point: Next Generation Computer Arithmetic_](
https://www.youtube.com/watch?v=aP0Y1uAA-2Y).

At the moment there are no major hardware implementations of the posit
standard. SoftPosit is an implementation of the posit standard written in
the C programming language. This crate consists of bindings to the
SoftPosit library.

## Crate's Philosophy

The types and methods exposed in this library are thin wrappers for
SoftPosit's API, nothing more and nothing less. This means that operations
that are not implemented in SoftPosit, such as trigonometric functions and
exponentials, are not implemented by this library.

The bindings provided by this crate are meant to be
[type-safe](https://doc.rust-lang.org/stable/book/ch19-01-unsafe-rust.html)
and conform to the
[Rust API Guidelines](
https://rust-lang.github.io/api-guidelines/about.html). This means that:

1. Type-safety should not be a concern for users of this crate, only for
   those implementing it.
2. The functions exposed by SoftPosit are all hooked-up to the appropriate
   Rust traits.
3. This library does not expose internal implementation details. Users can
   only access SoftPosit's API via a limited, type-safe interface.

Moreover, this bindings are meant to be as flexible as possible and the
interfaces for posit types are meant to mimic `f64`'s interface.

## Usage

Posit numbers can be construct from Rust's primitive numeric types via the
`From` trait. Posit numbers can also be converted back to the primitive
numeric types via the `Into` trait:

* When converting posits to any numeric type, a finite value (a value that
  is not NaR) is converted to it's appropriate numeric value
* When converting posits to integer types (`i32`, `u32`, `i64`, etc.), NaR
  is converted to zero
* When converting posits to floating-point types (`f32` and `f64`), NaR is
  converted to NaN

For deep learning, please use the quire types:

```
use posit_rs::{Posit32, Quire32};

fn main() {
    // Convert doubles to posits
    let a = Posit32::from(1.02783203125f64);
    let b = Posit32::from(0.987060546875f64);
    let c = Posit32::from(0.4998779296875f64);
    let d = Posit32::from(0.8797607421875f64);

    // Set quire to 0
    let mut q = Quire32::CLEAR;

    // Accumulate products without roundings
    q = q.dot_product_add(a, b);
    q = q.dot_product_add(c, d);

    // Convert back to posit
    let p: Posit32 = q.into();

    // Check the answer
    println!("{}", f64::from(p));
}
```

## TODO

* Make the bindings compile
* Implement tests
* Implement `Display`, `LowerExp` and `UpperExp` for the posit types
* Implement bindings for the flexible posit and quire types
* Implement bindings for `posit64_t`

## Licensing

Copyright (C) 2021 Pablo. Free use of this software is granted under the
terms of the GPL-3.0 License.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the GPL-3.0
license, shall be dual licensed as above, without any additional terms or
conditions.

