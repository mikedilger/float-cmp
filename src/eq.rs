// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

use std::{f32,f64};
use super::Ulps;

/// ApproxEq is a trait for approximate equality comparisons.
/// The associated type defines a margin within which two values are to be
/// considered approximately equal.
pub trait ApproxEq {
    type Margin;

    /// This method tests for `self` and `other` values to be approximately equal
    /// within `margin`.
    fn approx_eq(&self, other: &Self, margin: &Self::Margin) -> bool;

    /// This method tests for `self` and `other` values to be not approximately
    /// equal within `margin`.
    fn approx_ne(&self, other: &Self, margin: &Self::Margin) -> bool {
        !self.approx_eq(other, margin)
    }
}

#[derive(Debug, Clone)]
pub struct F32Margin {
    pub epsilon: f32,
    pub ulps: i32
}
impl Default for F32Margin {
    #[inline]
    fn default() -> F32Margin {
        F32Margin {
            epsilon: f32::EPSILON,
            ulps: 4
        }
    }
}
impl F32Margin {
    #[inline]
    pub fn zero() -> F32Margin {
        F32Margin {
            epsilon: 0.0,
            ulps: 0
        }
    }
}

impl ApproxEq for f32 {
    type Margin = F32Margin;

    fn approx_eq(&self, other: &f32, margin: &F32Margin) -> bool {
        // Check for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        *self==*other ||

        // Perform epsilon comparison next
            ((*self - *other).abs() <= margin.epsilon) ||

        {
            // Perform ulps comparion last
            let diff: i32 = self.ulps(other);
            diff.abs() <= margin.ulps
        }
    }
}

#[test]
fn f32_approx_eq_test1() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0000000000000005551115123125783_f32;
    assert!(f != g); // Should not be directly equal
    assert!(f.approx_eq(&g, &F32Margin { ulps: 0, ..Default::default() }) == true);
}
#[test]
fn f32_approx_eq_test2() {
    let f: f32 = 0.0_f32;
    let g: f32 = -0.0_f32;
    assert!(f.approx_eq(&g, &F32Margin { ulps: 0, ..Default::default() }) == true);
}
#[test]
fn f32_approx_eq_test3() {
    let f: f32 = 0.0_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, &F32Margin { ulps: 0, ..Default::default() }) == true);
}
#[test]
fn f32_approx_eq_test4() {
    let f: f32 = 0.00001_f32;
    let g: f32 = 0.00000000000000001_f32;
    assert!(f.approx_eq(&g, &F32Margin { ulps: 0, ..Default::default() }) == false);
}
#[test]
fn f32_approx_eq_test5() {
    let f: f32 = 0.1_f32;
    let mut sum: f32 = 0.0_f32;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f32 = f * 10.0_f32;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_eq(&product, &F32Margin { ulps: 1, ..Default::default() }) == true);
    assert!(sum.approx_eq(&product, &F32Margin::zero()) == false);
}
#[test]
fn f32_approx_eq_test6() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    assert!(x.approx_eq(&y, &F32Margin { epsilon: 0.0, ulps: 2}) == true); // 2 ulps does it
    // epsilon method no good here:
    assert!(x.approx_eq(&y, &F32Margin { epsilon: 1000.0 * f32::EPSILON, ulps: 0}) == false);
}

#[derive(Debug, Clone)]
pub struct F64Margin {
    pub epsilon: f64,
    pub ulps: i64
}
impl Default for F64Margin {
    #[inline]
    fn default() -> F64Margin {
        F64Margin {
            epsilon: f64::EPSILON,
            ulps: 4
        }
    }
}
impl F64Margin {
    #[inline]
    pub fn zero() -> F64Margin {
        F64Margin {
            epsilon: 0.0,
            ulps: 0
        }
    }
}

impl ApproxEq for f64 {
    type Margin = F64Margin;

    fn approx_eq(&self, other: &f64, margin: &F64Margin) -> bool {
        // Check for exact equality first. This is often true, and so we get the
        // performance benefit of only doing one compare in most cases.
        *self==*other ||

        // Perform epsilon comparison next
            ((*self - *other).abs() <= margin.epsilon) ||

        {
            // Perform ulps comparion last
            let diff: i64 = self.ulps(other);
            diff.abs() <= margin.ulps
        }
    }
}

#[test]
fn f64_approx_eq_test1() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0000000000000005551115123125783_f64;
    assert!(f != g); // Should not be directly equal
    let margin = F64Margin { epsilon: 3.0 * f64::EPSILON, ulps: 0 };
    assert!(f.approx_eq(&g, &margin) == true); // 3e is enough
    // ulps test wont ever call these equal
}
#[test]
fn f64_approx_eq_test2() {
    let f: f64 = 0.0_f64;
    let g: f64 = -0.0_f64;
    let margin = F64Margin { epsilon: f64::EPSILON, ulps: 0 };
    assert!(f.approx_eq(&g, &margin) == true);
}
#[test]
fn f64_approx_eq_test3() {
    let f: f64 = 0.0_f64;
    let g: f64 = 1e-17_f64;
    let margin = F64Margin { epsilon: f64::EPSILON, ulps: 0 };
    assert!(f.approx_eq(&g, &margin) == true);
}
#[test]
fn f64_approx_eq_test4() {
    let f: f64 = 0.00001_f64;
    let g: f64 = 0.00000000000000001_f64;
    let margin = F64Margin { epsilon: f64::EPSILON, ulps: 0 };
    assert!(f.approx_eq(&g, &margin) == false);
}
#[test]
fn f64_approx_eq_test5() {
    let f: f64 = 0.1_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    let margin = F64Margin { epsilon: f64::EPSILON, ulps: 0 };
    assert!(sum.approx_eq(&product, &margin) == true);
    let margin = F64Margin { epsilon: 0.0, ulps: 1 };
    assert!(sum.approx_eq(&product, &margin) == true);
}
#[test]
fn f64_approx_eq_test6() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    let margin = F64Margin { epsilon: 0.0, ulps: 3 };
    assert!(x.approx_eq(&y, &margin) == true);
}
