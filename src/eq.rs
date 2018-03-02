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
    /// using either the ULPs method or an epsilon method. The epsilon method is
    /// used when zeroes are involved or the signs are opposite.  Otherwise the ULPs
    /// method is used. It is recommended to use a smallish integer for ulps, and
    /// a smallish multiple of your floating point type's EPSILON for epsilon.
    fn approx_eq(&self, other: &Self, ulps: <Self::Flt as Ulps>::U, epsilon: Self::Flt)
                 -> bool;

    /// This method tests for `self` and `other` values to be not approximately equal
    /// using either the ULPs method or an epsilon method. The epsilon method is
    /// used when zeroes are involved or the signs are opposite.  Otherwise the ULPs
    /// method is used. It is recommended to use a smallish integer for ulps, and
    /// a smallish multiple of your floating point type's EPSILON for epsilon.
    fn approx_ne(&self, other: &Self, ulps: <Self::Flt as Ulps>::U, epsilon: Self::Flt)
                 -> bool
    {
        !self.approx_eq(other, ulps, epsilon)
    }
}

impl ApproxEq for f32 {
    type Flt = f32;

    fn approx_eq(&self, other: &f32, ulps: i32, epsilon: f32) -> bool {
        // Compare for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        if *self==*other { return true; }

        // Handle differing signs and zeroes with an epsilon method
        if self.signum() != other.signum() || *self==0.0 || *other==0.0 {
            return (*self - *other).abs() < epsilon;
        }

        let diff: i32 = self.ulps(other);
        diff >= -ulps && diff <= ulps
    }
}

#[test]
fn f32_approx_eq_test1() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0000000000000005551115123125783_f32;
    assert!(f != g); // Should not be directly equal
    assert!(f.approx_eq(&g, 10, 10.0 * f32::EPSILON) == true);
}
#[test]
fn f32_approx_eq_test2() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0_f32;
    assert!(f.approx_eq(&g, 1, 10.0 * f32::EPSILON) == true);
}
#[test]
fn f32_approx_eq_test3() {
    let f: f32 = 0.0_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, 10, 10.0 * f32::EPSILON) == true);
}
#[test]
fn f32_approx_eq_test4() {
    let f: f32 = 0.00001_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, 10, 10.0 * f32::EPSILON) == false);
}
#[test]
fn f32_approx_eq_test5() {
    let f: f32 = 0.1_f32;
    let mut sum: f32 = 0.0_f32;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f32 = f * 10.0_f32;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq(&product, 1, 10.0 * f32::EPSILON) == true); // But should be close
    assert!(sum.approx_eq(&product, 0, 10.0 * f32::EPSILON) == false);
}
#[test]
fn f32_approx_eq_test6() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    assert!(x.approx_eq(&y, 2, 10.0 * f32::EPSILON) == true);
    assert!(x.approx_eq(&y, 1, 10.0 * f32::EPSILON) == false);
}

impl ApproxEq for f64 {
    type Flt = f64;

    fn approx_eq(&self, other: &f64, ulps: i64, epsilon: f64) -> bool {
        // Compare for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        if *self==*other { return true; }

        // Handle differing signs and zeroes with an epsilon method
        if self.signum() != other.signum() || *self==0.0 || *other==0.0 {
            return (*self - *other).abs() < epsilon;
        }

        let diff: i64 = self.ulps(other);
        diff >= -ulps && diff <= ulps
    }
}

#[test]
fn f64_approx_eq_test1() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0000000000000005551115123125783_f64;
    assert!(f != g); // Should not be directly equal
    assert!(f.approx_eq(&g, 10, 10.0 * f64::EPSILON) == true);
}
#[test]
fn f64_approx_eq_test2() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0_f64;
    assert!(f.approx_eq(&g, 1, 10.0 * f64::EPSILON) == true);
}
#[test]
fn f64_approx_eq_test3() {
    let f: f64 = 0.0_f64;
    let g: f64 = 1e-17_f64;
    assert!(f.approx_eq(&g, 10, 10.0 * f64::EPSILON) == true);
}
#[test]
fn f64_approx_eq_test4() {
    let f: f64 = 0.00001_f64;
    let g: f64 = 0.00000000000000001_f64;
    assert!(f.approx_eq(&g, 10, 10.0 * f64::EPSILON) == false);
}
#[test]
fn f64_approx_eq_test5() {
    let f: f64 = 0.1_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq(&product, 1, 10.0 * f64::EPSILON) == true); // But should be close
    assert!(sum.approx_eq(&product, 0, 10.0 * f64::EPSILON) == false);
}
#[test]
fn f64_approx_eq_test6() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_eq(&y, 3, 10.0 * f64::EPSILON) == true);
    assert!(x.approx_eq(&y, 2, 10.0 * f64::EPSILON) == false);
}
