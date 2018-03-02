// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

//! float-cmp defines traits for approximate comparison of floating point types which have fallen
//! away from exact equality due to the limited precision available within floating point
//! representations. Implementations of these traits are provided for `f32` and `f64` types.
//!
//! Two methods of comparison are provided. The first, `ApproxEqUlps` and `ApproxOrdUlps`, consider
//! two comparands equal if the count of floating point representations between them is
//! below a specified bound. This works well in most cases.
//!
//! The second method of comparison, `ApproxEqRatio`, considers two comparands equal if the ratio of
//! the difference between them to the larger is below some specified bound. This handles many of
//! the cases that the former type of comparison doesn't handle well.
//!
//! To help choose which comparison method to use, and to learn many suprising facts and oddities
//! about floating point numbers, please refer to the following excellent website:
//! https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/
//!
//! The trait `Ulps` is also defined.
//!
//! Floating point operations must round answers to the nearest representable number.  Multiple
//! operations may result in an answer different from what you expect.  In the following example,
//! the assert will fail, even though the printed output says "0.45 == 0.45":
//!
//! ```should_fail
//!   let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
//!   let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
//!   println!("{} == {}", a, b);
//!   assert!(a==b)  // Fails, because they are not exactly equal
//! ```
//!
//! This fails because the correct answer to most operations isn't exactly representable, and so your
//! computer's processor chooses to represent the answer with the closest value it has available.
//! This introduces error, and this error can accumulate as multiple operations are performed.
//!
//! With `ApproxEqUlps`, we can get the answer we intend:
//!
//! ```
//!   # extern crate float_cmp;
//!   # use float_cmp::ApproxEqUlps;
//!   # fn main() {
//!   let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
//!   let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
//!   println!("{} == {}", a, b);
//!   assert!(a.approx_eq_ulps(&b,2)) // They are equal, within 2 ulps
//!   # }
//! ```
//!
//! We use the term ULP (units of least precision, or units in the last place) to mean the
//! difference between two adjacent floating point representations (adjacent meaning that there is
//! no floating point number between them). This term is borrowed from prior work (personally I
//! would have chosen "quanta"). The size of an ULP (measured as a float) varies
//! depending on the exponents of the floating point numbers in question, but this is quite useful,
//! for it is the non-variation of a fixed epsilon (e.g. 0.0000001) which causes epsilon-based
//! comparisons to so often fail with more extreme floating point values.
//!
//! Fixed epsilon systems of comparison tend to work well only on numbers within certain ranges.
//! It may seem reasonable to expect numbers that differ by less than 0.000001 to be equal, but
//! this does not always work well (consider comparing -0.0000000028 to +0.00000097).
//!
//! You can implement `ApproxEqUlps` for your own complex types. The trait and type parameter
//! notation can be a bit tricky, so here is an example:
//!
//! ```
//! use float_cmp::{ApproxEqUlps, Ulps};
//!
//! pub struct Vec2<F> {
//!   pub x: F,
//!   pub y: F,
//! }
//!
//! impl<F: Ulps + ApproxEqUlps<Flt=F>> ApproxEqUlps for Vec2<F> {
//!   type Flt = F;
//!
//!   fn approx_eq_ulps(&self, other: &Self, ulps: <<F as ApproxEqUlps>::Flt as Ulps>::U) -> bool {
//!     self.x.approx_eq_ulps(&other.x, ulps)
//!       && self.y.approx_eq_ulps(&other.y, ulps)
//!   }
//! }
//! ```

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
