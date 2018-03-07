// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

use std::{f32,f64};
use super::Ulps;

/// ApproxEq is a trait for approximate equality comparisons. The associated type Flt is a
/// floating point type which implements Ulps, and is required so that this trait can be
/// implemented for compound types (e.g. vectors),/ not just for the floats themselves.
pub trait ApproxEq {
    type Flt: Ulps;

    /// This method tests for `self` and `other` values to be approximately equal
    /// using two methods: epsilon and ulps.  If the values differ by less than the
    /// given epsilon, they will be considered equal. If the values differ by more
    /// than epsilon, but by less than the given ulps, they will also be considered
    /// equal. Otherwise they are unequal.
    ///
    /// Note that very small values of differing signs may pass as equal under the
    /// epsilon method. The epsilon method is very useful for these cases and for
    /// handling zeroes. The ulps method helps for larger numbers where the spacing
    /// between floating point representations gets larger.
    fn approx_eq(&self, other: &Self, epsilon: Self::Flt, ulps: <Self::Flt as Ulps>::U)
                 -> bool;

    /// This method tests for `self` and `other` values to be not approximately equal
    /// using two methods: epsilon and ulps.  If the values differ by less than the
    /// given epsilon, they will be considered equal. If the values differ by more
    /// than epsilon, but by less than the given ulps, they will also be considered
    /// equal. Otherwise they are unequal.
    ///
    /// Note that very small values of differing signs may pass as equal under the
    /// epsilon method. The epsilon method is very useful for these cases and for
    /// handling zeroes. The ulps method helps for larger numbers where the spacing
    /// between floating point representations gets larger.
    fn approx_ne(&self, other: &Self, epsilon: Self::Flt, ulps: <Self::Flt as Ulps>::U)
                 -> bool
    {
        !self.approx_eq(other, epsilon, ulps)
    }
}

impl ApproxEq for f32 {
    type Flt = f32;

    fn approx_eq(&self, other: &f32, epsilon: f32, ulps: i32) -> bool {
        // Check for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        *self==*other ||

        // Perform epsilon comparison next
            ((*self - *other).abs() <= epsilon) ||

        {
            // Perform ulps comparion last
            let diff: i32 = self.ulps(other);
            -ulps <= diff && diff <= ulps
        }
    }
}

#[test]
fn f32_approx_eq_test1() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0000000000000005551115123125783_f32;
    assert!(f != g); // Should not be directly equal
    assert!(f.approx_eq(&g, f32::EPSILON, 0) == true);
}
#[test]
fn f32_approx_eq_test2() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0_f32;
    assert!(f.approx_eq(&g, f32::EPSILON, 0) == true);
}
#[test]
fn f32_approx_eq_test3() {
    let f: f32 = 0.0_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, f32::EPSILON, 0) == true);
}
#[test]
fn f32_approx_eq_test4() {
    let f: f32 = 0.00001_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, f32::EPSILON, 0) == false);
}
#[test]
fn f32_approx_eq_test5() {
    let f: f32 = 0.1_f32;
    let mut sum: f32 = 0.0_f32;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f32 = f * 10.0_f32;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq(&product, f32::EPSILON, 1) == true); // But should be close
    assert!(sum.approx_eq(&product, 0.0, 0) == false);
}
#[test]
fn f32_approx_eq_test6() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    assert!(x.approx_eq(&y, 0.0, 2) == true); // 2 ulps does it
    assert!(x.approx_eq(&y, 1000.0 * f32::EPSILON, 0) == false); // epsilon method no good here
}

impl ApproxEq for f64 {
    type Flt = f64;

    fn approx_eq(&self, other: &f64, epsilon: f64, ulps: i64) -> bool {
        // Check for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        *self==*other ||

        // Perform epsilon comparison next
            ((*self - *other).abs() <= epsilon) ||

        {
            // Perform ulps comparion last
            let diff: i64 = self.ulps(other);
            -ulps <= diff && diff <= ulps
        }
    }
}

#[test]
fn f64_approx_eq_test1() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0000000000000005551115123125783_f64;
    assert!(f != g); // Should not be directly equal
    assert!(f.approx_eq(&g, 3.0 * f64::EPSILON, 0) == true); // 3e is enough
    // ulps test wont ever call these equal
}
#[test]
fn f64_approx_eq_test2() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0_f64;
    assert!(f.approx_eq(&g, f64::EPSILON, 0) == true);
}
#[test]
fn f64_approx_eq_test3() {
    let f: f64 = 0.0_f64;
    let g: f64 = 1e-17_f64;
    assert!(f.approx_eq(&g, f64::EPSILON, 0) == true);
}
#[test]
fn f64_approx_eq_test4() {
    let f: f64 = 0.00001_f64;
    let g: f64 = 0.00000000000000001_f64;
    assert!(f.approx_eq(&g, f64::EPSILON, 0) == false);
}
#[test]
fn f64_approx_eq_test5() {
    let f: f64 = 0.1_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq(&product, f64::EPSILON, 0) == true);
    assert!(sum.approx_eq(&product, 0.0, 1) == true);
}
#[test]
fn f64_approx_eq_test6() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_eq(&y, 0.0, 3) == true);
}
