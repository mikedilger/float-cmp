// Copyright 2014 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

//! float-cmp defines traits for approximate comparison of floating point types which have fallen
//! away from exact equality due to rounding and inaccuracies within the floating point unit of your
//! computer's processor. Implementations of these traits are provided for `f32` and `f64` types.
//!
//! Two methods of comparison are provided. The first, `ApproxEqUlps` and `ApproxOrdUlps`, consider
//! two comparands equal if the number of representable floating point numbers between them is
//! below a specified bound. This works well in most cases.
//!
//! The second method of comparison, `ApproxEqRatio`, considers two comparands equal if the ratio of
//! the difference between them to the larger is below some specified bound.  This handles many of
//! the cases that the former type of comparison doesn't handle well.
//!
//! To help choose which comparison method to use, and to learn many suprising facts and oddities
//! about floating point numbers, please refer to the following excellent website:
//! https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/
//!
//! The trait `Ulps` is also defined as a prerequisite for `ApproxEqUlps` and `ApproxOrdUlps`.
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
//! This fails due to rounding and inaccuracies within the floating point unit of your processor.
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
//! no floating point number between them).  The size of an ULP (measured as a float) varies
//! depending on the exponents of the floating point numbers in question, but this is quite useful,
//! for it is the non-variation of a fixed epsilon (e.g. 0.0000001) which causes epsilon-based
//! comparisons to so often fail with more extreme floating point values.
//!
//! Fixed epsilon systems of comparison tend to work well only on numbers within certain ranges.
//! It may seem reasonable to expect numbers that differ by less than 0.000001 to be equal, but
//! this does not always work well (consider comparing -0.0000000028 to +0.00000097).

extern crate num_traits as num;
use num::Zero;

use std::mem;
use std::cmp::{Ordering,PartialOrd};
use std::ops::{Sub,Div};

/// A trait for floating point numbers which computes the number of representable
/// values or ULPs (Units of Least Precision) that separate the two given values.
pub trait Ulps {
    type U;

    /// The number of representable values or ULPs (Units of Least Precision) that
    /// separate `self` and `other`.  The result `U` is an integral value, and will
    /// be zero if `self` and `other` are exactly equal.
    fn ulps(&self, other: &Self) -> <Self as Ulps>::U;
}

impl Ulps for f32 {
    type U = i32;

    fn ulps(&self, other: &f32) -> i32 {

        // IEEE754 defined floating point storage representation to
        // maintain their order when their bit patterns are interpreted as
        // integers.  This is a huge boon to the task at hand, as we can
        // (unsafely) cast to integers to find out how many ULPs apart any
        // two floats are

        // Setup integer representations of the input
        let ai32: i32 = unsafe { mem::transmute(*self) };
        let bi32: i32 = unsafe { mem::transmute(*other) };

        ai32.wrapping_sub(bi32)
    }
}

#[test]
fn f32_ulps_test1() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    println!("DIST IS {}",x.ulps(&y));
    assert!(x.ulps(&y) == -2);
}

#[test]
fn f32_ulps_test2() {
    let pzero: f32 = unsafe { mem::transmute(0x00000000_u32) };
    let nzero: f32 = unsafe { mem::transmute(0x80000000_u32) };
    println!("DIST IS {}",pzero.ulps(&nzero));
    assert!(pzero.ulps(&nzero) == -2147483648);
}
#[test]
fn f32_ulps_test3() {
    let pinf: f32 = unsafe { mem::transmute(0x7f800000_u32) };
    let ninf: f32 = unsafe { mem::transmute(0xff800000_u32) };
    println!("DIST IS {}",pinf.ulps(&ninf));
    assert!(pinf.ulps(&ninf) == -2147483648);
}

#[test]
fn f32_ulps_test4() {
    let x: f32 = unsafe { mem::transmute(0x63a7f026_u32) };
    let y: f32 = unsafe { mem::transmute(0x63a7f023_u32) };
    println!("DIST IS {}",x.ulps(&y));
    assert!(x.ulps(&y) == 3);
}

impl Ulps for f64 {
    type U = i64;

    fn ulps(&self, other: &f64) -> i64 {

        // IEEE754 defined floating point storage representation to
        // maintain their order when their bit patterns are interpreted as
        // integers.  This is a huge boon to the task at hand, as we can
        // (unsafely) cast to integers to find out how many ULPs apart any
        // two floats are

        // Setup integer representations of the input
        let ai64: i64 = unsafe { mem::transmute(*self) };
        let bi64: i64 = unsafe { mem::transmute(*other) };

        ai64.wrapping_sub(bi64)
    }
}

#[test]
fn f64_ulps_test1() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.00000001_f64;
    println!("DIST IS {}",x.ulps(&y));
    assert!(x.ulps(&y) == -86);
}

#[test]
fn f64_ulps_test2() {
    let pzero: f64 = unsafe { mem::transmute(0x0000000000000000_u64) };
    let nzero: f64 = unsafe { mem::transmute(0x8000000000000000_u64) };
    println!("DIST IS {}",pzero.ulps(&nzero));
    assert!(pzero.ulps(&nzero) == -9223372036854775808i64);
}
#[test]
fn f64_ulps_test3() {
    let pinf: f64 = unsafe { mem::transmute(0x7f80000000000000_u64) };
    let ninf: f64 = unsafe { mem::transmute(0xff80000000000000_u64) };
    println!("DIST IS {}",pinf.ulps(&ninf));
    assert!(pinf.ulps(&ninf) == -9223372036854775808i64);
}

#[test]
fn f64_ulps_test4() {
    let x: f64 = unsafe { mem::transmute(0xd017f6cc63a7f026_u64) };
    let y: f64 = unsafe { mem::transmute(0xd017f6cc63a7f023_u64) };
    println!("DIST IS {}",x.ulps(&y));
    assert!(x.ulps(&y) == 3);
}


/// ApproxEqUlps is a trait for approximate equality comparisons, and is defined only
/// for floating point types.
pub trait ApproxEqUlps : Ulps {
    /// This method tests for `self` and `other` values to be approximately equal
    /// within ULPs (Units of Least Precision) floating point representations.
    fn approx_eq_ulps(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool;

    /// This method tests for `self` and `other` values to be not approximately
    /// equal within ULPs (Units of Least Precision) floating point representations.
    #[inline]
    fn approx_ne_ulps(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool {
        !self.approx_eq_ulps(other, ulps)
    }
}

impl ApproxEqUlps for f32 {
    fn approx_eq_ulps(&self, other: &f32, ulps: i32) -> bool {
        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if *self==*other { return true; }

        // Handle differing signs as a special case, even if
        // they are very close, most people consider them
        // unequal.
        if *self>0_f32 && *other<0_f32 { return false; }
        if *self<0_f32 && *other>0_f32 { return false; }

        let diff: i32 = self.ulps(other);
        diff >= -ulps && diff <= ulps
    }
}

#[test]
fn f32_approx_eq_test1() {
    let f: f32 = 0.1_f32;
    let mut sum: f32 = 0.0_f32;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f32 = f * 10.0_f32;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq_ulps(&product,1) == true); // But should be close
    assert!(sum.approx_eq_ulps(&product,0) == false);
}
#[test]
fn f32_approx_eq_test2() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_eq_ulps(&y,2) == true);
    assert!(x.approx_eq_ulps(&y,1) == false);
}
#[test]
fn f32_approx_eq_test_zeroes() {
    let x: f32 = 0.0_f32;
    let y: f32 = -0.0_f32;
    assert!(x.approx_eq_ulps(&y,0) == true);
}

impl ApproxEqUlps for f64 {
    fn approx_eq_ulps(&self, other: &f64, ulps: i64) -> bool {
        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if *self==*other { return true; }

        // Handle differing signs as a special case, even if
        // they are very close, most people consider them
        // unequal.
        if *self>0_f64 && *other<0_f64 { return false; }
        if *self<0_f64 && *other>0_f64 { return false; }

        let diff: i64 = self.ulps(other);
        diff >= -ulps && diff <= ulps
    }
}

#[test]
fn f64_approx_eq_test1() {
    let f: f64 = 0.1_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq_ulps(&product,1) == true); // But should be close
    assert!(sum.approx_eq_ulps(&product,0) == false);
}
#[test]
fn f64_approx_eq_test2() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_eq_ulps(&y,3) == true);
    assert!(x.approx_eq_ulps(&y,2) == false);
}
#[test]
fn f64_approx_eq_test_zeroes() {
    let x: f64 = 0.0_f64;
    let y: f64 = -0.0_f64;
    assert!(x.approx_eq_ulps(&y,0) == true);
}

/// ApproxOrdUlps is for sorting floating point values where approximate equality
/// is considered equal.
pub trait ApproxOrdUlps: ApproxEqUlps {
    /// This method returns an ordering between `self` and `other` values
    /// if one exists, where Equal is returned if they are approximately
    /// equal within `ulps` floating point representations.  See module
    /// documentation for an understanding of `ulps`
    fn approx_cmp(&self, other: &Self, ulps: <Self as Ulps>::U) -> Ordering;

    /// This method tests less than (for `self` < `other`), where values
    /// within `ulps` of each other are not less than.  See module
    /// documentation for an understanding of `ulps`.
    #[inline]
    fn approx_lt(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool {
        match self.approx_cmp(other, ulps) {
            Ordering::Less => true,
            _ => false,
        }
    }

    /// This method tests less than or equal to (for `self` <= `other`)
    /// where values within `ulps` are equal.  See module documentation
    /// for an understanding of `ulps`.
    #[inline]
    fn approx_le(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool {
        match self.approx_cmp(other, ulps) {
            Ordering::Less | Ordering::Equal => true,
            _ => false,
        }
    }

    /// This method tests greater than (for `self` > `other`)
    /// where values within `ulps` are not greater than.  See module
    /// documentation for an understanding of `ulps`
    #[inline]
    fn approx_gt(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool {
        match self.approx_cmp(other, ulps) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    /// This method tests greater than or equal to (for `self` > `other`)
    /// where values within `ulps` are equal.  See module documentation
    /// for an understanding of `ulps`.
    #[inline]
    fn approx_ge(&self, other: &Self, ulps: <Self as Ulps>::U) -> bool {
        match self.approx_cmp(other, ulps) {
            Ordering::Greater | Ordering::Equal => true,
            _ => false,
        }
    }
}

impl ApproxOrdUlps for f32 {
    fn approx_cmp(&self, other: &f32, ulps: <Self as Ulps>::U) -> Ordering {

        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if self==other { return Ordering::Equal; }

        // Handle differing signs as a special case, even if
        // they are very close, most people consider them
        // unequal.
        if *self>0_f32 && *other<0_f32 { return Ordering::Greater; }
        if *self<0_f32 && *other>0_f32 { return Ordering::Less }

        let diff: i32 = self.ulps(other);
        match diff {
            x if x > 0 && x <= ulps => Ordering::Equal,
            x if x > 0 => Ordering::Greater,
            x if x < 0 && x >= -ulps => Ordering::Equal,
            x if x < 0 => Ordering::Less,
            _ => Ordering::Equal
        }
    }
}

#[test]
fn f32_approx_cmp_test1() {
    let f: f32 = 0.1_f32;
    let mut sum: f32 = 0.0_f32;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f32 = f * 10.0_f32;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_cmp(&product,1) == Ordering::Equal); // But should be close
    assert!(sum.approx_cmp(&product,0) != Ordering::Equal);
    assert!(product.approx_cmp(&sum,0) != Ordering::Equal);
}
#[test]
fn f32_approx_cmp_test2() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_cmp(&y,2) == Ordering::Equal);
    assert!(x.approx_cmp(&y,1) == Ordering::Less);
    assert!(y.approx_cmp(&x,1) == Ordering::Greater);
}

impl ApproxOrdUlps for f64 {
    fn approx_cmp(&self, other: &f64, ulps: <Self as Ulps>::U) -> Ordering {

        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if self==other { return Ordering::Equal; }

        // Handle differing signs as a special case, even if
        // they are very close, most people consider them
        // unequal.
        if *self>0_f64 && *other<0_f64 { return Ordering::Greater; }
        if *self<0_f64 && *other>0_f64 { return Ordering::Less }

        let diff: i64 = self.ulps(other);
        match diff {
            x if x > 0 && x <= ulps => Ordering::Equal,
            x if x > 0 => Ordering::Greater,
            x if x < 0 && x >= -ulps => Ordering::Equal,
            x if x < 0 => Ordering::Less,
            _ => Ordering::Equal
        }
    }
}

#[test]
fn f64_approx_cmp_test1() {
    let f: f64 = 0.000000001_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_cmp(&product,1) == Ordering::Equal); // But should be close
    assert!(sum.approx_cmp(&product,0) != Ordering::Equal);
    assert!(product.approx_cmp(&sum,0) != Ordering::Equal);
}
#[test]
fn f64_approx_cmp_test2() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_cmp(&y,3) == Ordering::Equal);
    assert!(x.approx_cmp(&y,2) == Ordering::Less);
    assert!(y.approx_cmp(&x,2) == Ordering::Greater);
}

/// ApproxEqRatio is a trait for approximate equality comparisons bounding the ratio
/// of the difference to the larger.
pub trait ApproxEqRatio : Div<Output = Self> + Sub<Output = Self> + PartialOrd + Zero
    + Sized + Copy
{
    /// This method tests if `self` and `other` are nearly equal by bounding the
    /// difference between them to some number much less than the larger of the two.
    /// This bound is set as the ratio of the difference to the larger.
    fn approx_eq_ratio(&self, other: &Self, ratio: Self) -> bool {
        if *self < Self::zero() && *other > Self::zero() { return false; }
        if *self > Self::zero() && *other < Self::zero() { return false; }
        let (smaller,larger) = if *self < *other {
            (self,other)
        } else {
            (other,self)
        };
        let difference: Self = larger.sub(*smaller);
        let actual_ratio: Self = difference.div(*larger);
        actual_ratio < ratio
    }

    /// This method tests if `self` and `other` are not nearly equal by bounding the
    /// difference between them to some number much less than the larger of the two.
    /// This bound is set as the ratio of the difference to the larger.
    #[inline]
    fn approx_ne_ratio(&self, other: &Self, ratio: Self) -> bool {
        !self.approx_eq_ratio(other, ratio)
    }
}

impl ApproxEqRatio for f32 { }

#[test]
fn f32_approx_eq_ratio_test1() {
    let x: f32 = 0.00004_f32;
    let y: f32 = 0.00004001_f32;
    assert!(x.approx_eq_ratio(&y, 0.00025));
    assert!(y.approx_eq_ratio(&x, 0.00025));
    assert!(x.approx_ne_ratio(&y, 0.00024));
    assert!(y.approx_ne_ratio(&x, 0.00024));
}

#[test]
fn f32_approx_eq_ratio_test2() {
    let x: f32 = 0.00000000001_f32;
    let y: f32 = 0.00000000005_f32;
    assert!(x.approx_eq_ratio(&y, 0.81));
    assert!(y.approx_ne_ratio(&x, 0.79));
}

#[test]
fn f32_approx_eq_ratio_test_zero_eq_zero_returns_true() {
    let x: f32 = 0.0_f32;
    assert!(x.approx_eq_ratio(&x,0.1) == true);
}

#[test]
fn f32_approx_eq_ratio_test_zero_ne_zero_returns_false() {
    let x: f32 = 0.0_f32;
    assert!(x.approx_ne_ratio(&x,0.1) == false);
}

#[test]
fn f32_approx_eq_ratio_test_negative_numbers() {
    let x: f32 = -3.0_f32;
    let y: f32 = -4.0_f32;
    // -3 and -4 should not be equal at a ratio of 0.1
    assert!(x.approx_eq_ratio(&y,0.1) == false);
}

impl ApproxEqRatio for f64 { }

#[test]
fn f64_approx_eq_ratio_test1() {
    let x: f64 = 0.000000004_f64;
    let y: f64 = 0.000000004001_f64;
    assert!(x.approx_eq_ratio(&y, 0.00025));
    assert!(y.approx_eq_ratio(&x, 0.00025));
    assert!(x.approx_ne_ratio(&y, 0.00024));
    assert!(y.approx_ne_ratio(&x, 0.00024));
}

#[test]
fn f64_approx_eq_ratio_test2() {
    let x: f64 = 0.0000000000000001_f64;
    let y: f64 = 0.0000000000000005_f64;
    assert!(x.approx_eq_ratio(&y, 0.81));
    assert!(y.approx_ne_ratio(&x, 0.79));
}

#[test]
fn f64_approx_eq_ratio_test_zero_eq_zero_returns_true() {
    let x: f64 = 0.0_f64;
    assert!(x.approx_eq_ratio(&x,0.1) == true);
}

#[test]
fn f64_approx_eq_ratio_test_zero_ne_zero_returns_false() {
    let x: f64 = 0.0_f64;
    assert!(x.approx_ne_ratio(&x,0.1) == false);
}

#[test]
fn f64_approx_eq_ratio_test_negative_numbers() {
    let x: f64 = -3.0_f64;
    let y: f64 = -4.0_f64;
    // -3 and -4 should not be equal at a ratio of 0.1
    assert!(x.approx_eq_ratio(&y,0.1) == false);
}

