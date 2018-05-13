// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

//! # float-cmp
//!
//! float-cmp defines and implements traits for approximate comparison of floating point types
//! which have fallen away from exact equality due to the limited precision available within
//! floating point representations. Implementations of these traits are provided for `f32`
//! and `f64` types.
//!
//! When I was a kid in the '80s, the programming rule was "Never compare floating point
//! numbers". If you can follow that rule and still get the outcome you desire, then more
//! power to you. However, if you really do need to compare them, this crate provides a
//! reasonable way to do so.
//!
//! Another crate `efloat` (which as of this writing is still undergoing considerable
//! development) offers another solution by providing a floating point type that tracks its
//! error bounds as operations are performed on it, and thus can implement the `ApproxEq`
//! trait in this crate more accurately, without specifying a `Margin`.
//!
//! The recommended go-to solution (although it may not be appropriate in all cases) is the
//! `approx_eq()` function in the `ApproxEq` trait.  For `f32` and `f64`, the `F32Margin`
//! and `F64Margin` types are provided for specifying margins as both an epsilon value and
//! an ULPs value, and defaults are provided via `Default`.
//!
//! Several other traits are provided including `Ulps`, `ApproxEqUlps`, `ApproxOrdUlps`, and
//! `ApproxEqRatio`.
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
//!   # use float_cmp::{ApproxEq, F32Margin};
//!   # fn main() {
//!   let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
//!   let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
//!   println!("{} == {}", a, b);
//!   // They are equal, within 2 ulps
//!   assert!(a.approx_eq(&b, &F32Margin { epsilon: 0.0, ulps: 2}))
//!   # }
//! ```
//!
//! For most cases, I recommend you use a smallish integer for the `ulps` parameter (1 to 5
//! or so), and a similar small multiple of the floating point's EPSILON constant (1.0 to 5.0
//! or so), but there are *plenty* of cases where this is insufficient.
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
//! for many ranges of numbers, but not for others.
//!
//! ## Implementing these traits
//!
//! You can implement `ApproxEq` for your own complex types like this:
//!
//! ```
//! use float_cmp::ApproxEq;
//!
//! pub struct Vec2<F> {
//!   pub x: F,
//!   pub y: F,
//! }
//!
//! impl<M, F: ApproxEq<Margin=M>> ApproxEq for Vec2<F> {
//!   type Margin = M;
//!
//!   fn approx_eq(&self, other: &Self, margin: &M) -> bool
//!   {
//!     self.x.approx_eq(&other.x, margin)
//!       && self.y.approx_eq(&other.y, margin)
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
#[allow(deprecated)]
pub use self::ulps_ord::ApproxOrdUlps;

mod eq;
pub use self::eq::{ApproxEq, F32Margin, F64Margin};

mod ratio;
pub use self::ratio::ApproxEqRatio;
