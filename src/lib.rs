// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

//! # float-cmp
//!
//! float-cmp defines traits for approximate comparison of floating point types which have fallen
//! away from exact equality due to the limited precision available within floating point
//! representations. Implementations of these traits are provided for `f32` and `f64` types.
//!
//! Three methods of comparison are provided, but we recommend using the `ApproxEq` trait.
//! We have left the other traits in the library for compatability and until we are certain that
//! ApproxEq covers everything.
//!
//! ApproxEq compares two floating point numbers by selecting one of two techniques, depending
//! on the case. For two non-zero numbers of the same sign, the number of floating point
//! representations that separate them are counted (an integer number), and must fall below
//! a specifed bound that the caller supplies. This is an extremely fast operation. In all other
//! cases, the difference between the two numbers (absolute) must be less than a given epsilon
//! that the caller supplies.
//!
//! ## The problem
//!
//! Floating point operations must round answers to the nearest representable number. Multiple
//! operations may result in an answer different from what you expect. In the following example,
//! the assert will fail, even though the printed output says "0.45 == 0.45":
//!
//! ```should_panic
//!   # extern crate float_cmp;
//!   # use float_cmp::ApproxEq;
//!   # fn main() {
//!   let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
//!   let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
//!   println!("{} == {}", a, b);
//!   assert!(a==b)  // Fails, because they are not exactly equal
//!   # }
//! ```
//!
//! This fails because the correct answer to most operations isn't exactly representable, and so
//! your computer's processor chooses to represent the answer with the closest value it has
//! available. This introduces error, and this error can accumulate as multiple operations are
//! performed.
//!
//! ## The solution
//!
//! With `ApproxEq`, we can get the answer we intend:
//!
//! ```
//!   # extern crate float_cmp;
//!   # use float_cmp::ApproxEq;
//!   # fn main() {
//!   let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
//!   let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
//!   println!("{} == {}", a, b);
//!   assert!(a.approx_eq(&b, 2, 2.0 * ::std::f32::EPSILON)) // They are equal, within 2 ulps
//!   # }
//! ```
//!
//! I recommend you use a small integer for the `ulps` parameter (2 to 10 or so), and a
//! similar small multiple of the floating point's EPSILON constant (2.0 to 10.0 or so),
//! but please send feedback if you think you have better advice.
//!
//! ## Some explanation
//!
//! We use the term ULP (units of least precision, or units in the last place) to mean the
//! difference between two adjacent floating point representations (adjacent meaning that there is
//! no floating point number between them). This term is borrowed from prior work (personally I
//! would have chosen "quanta"). The size of an ULP (measured as a float) varies
//! depending on the exponents of the floating point numbers in question. That is a good thing,
//! because as numbers fall away from equality due to the imprecise nature of their representation,
//! they fall away in ULPs terms, not in absolute terms.  Pure epsilon-based comparisons are
//! absolute and thus don't map well to the nature of the additive error issue. They work fine
//! for many ranges of numbers, but not for others (consider comparing -0.0000000028
//! to +0.00000097).
//!
//! ## Implementing these traits
//!
//! You can implement `ApproxEq` for your own complex types. The trait and type parameter
//! notation can be a bit tricky, especially if your type is type parameterized around
//! floating point types.  So here is an example (you'll probably not specify the Copy trait
//! directly, but use some other NumTraits type floating point trait):
//!
//! ```
//! use float_cmp::{Ulps, ApproxEq};
//!
//! pub struct Vec2<F> {
//!   pub x: F,
//!   pub y: F,
//! }
//!
//! impl<F: Ulps + ApproxEq<Flt=F> + Copy> ApproxEq for Vec2<F> {
//!   type Flt = F;
//!
//!   fn approx_eq(&self, other: &Self, ulps: <<F as ApproxEq>::Flt as Ulps>::U,
//!                epsilon: <F as ApproxEq>::Flt) -> bool
//!   {
//!     self.x.approx_eq(&other.x, ulps, epsilon)
//!       && self.y.approx_eq(&other.y, ulps, epsilon)
//!   }
//! }
//! ```
//!
//! ## Inspiration
//!
//! This crate was inspired by this Random ASCII blog post:
//!
//! [https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/](https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/)

extern crate num_traits;

mod ulps;
pub use self::ulps::Ulps;

mod ulps_eq;
pub use self::ulps_eq::ApproxEqUlps;

mod ulps_ord;
pub use self::ulps_ord::ApproxOrdUlps;

mod eq;
pub use self::eq::ApproxEq;

mod ratio;
pub use self::ratio::ApproxEqRatio;
