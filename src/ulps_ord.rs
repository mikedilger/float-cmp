// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

use std::cmp::Ordering;
use std::num::{FpCategory};
use super::{Ulps, ApproxEqUlps};

/// ApproxOrdUlps is for sorting floating point values where approximate equality
/// is considered equal.
pub trait ApproxOrdUlps: ApproxEqUlps {
    /// This method returns an ordering between `self` and `other` values
    /// if one exists, where Equal is returned if they are approximately
    /// equal within `ulps` floating point representations.  See module
    /// documentation for an understanding of `ulps`
    fn approx_cmp_ulps(&self, other: &Self, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                       -> Ordering;

    /// This method tests less than (for `self` < `other`), where values
    /// within `ulps` of each other are not less than.  See module
    /// documentation for an understanding of `ulps`.
    #[inline]
    fn approx_lt_ulps(&self, other: &Self, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                      -> bool
    {
        match self.approx_cmp_ulps(other, ulps) {
            Ordering::Less => true,
            _ => false,
        }
    }

    /// This method tests less than or equal to (for `self` <= `other`)
    /// where values within `ulps` are equal.  See module documentation
    /// for an understanding of `ulps`.
    #[inline]
    fn approx_le_ulps(&self, other: &Self, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                      -> bool
    {
        match self.approx_cmp_ulps(other, ulps) {
            Ordering::Less | Ordering::Equal => true,
            _ => false,
        }
    }

    /// This method tests greater than (for `self` > `other`)
    /// where values within `ulps` are not greater than.  See module
    /// documentation for an understanding of `ulps`
    #[inline]
    fn approx_gt_ulps(&self, other: &Self, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                      -> bool
    {
        match self.approx_cmp_ulps(other, ulps) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    /// This method tests greater than or equal to (for `self` > `other`)
    /// where values within `ulps` are equal.  See module documentation
    /// for an understanding of `ulps`.
    #[inline]
    fn approx_ge_ulps(&self, other: &Self, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                      -> bool
    {
        match self.approx_cmp_ulps(other, ulps) {
            Ordering::Greater | Ordering::Equal => true,
            _ => false,
        }
    }
}

impl ApproxOrdUlps for f32 {
    fn approx_cmp_ulps(&self, other: &f32, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                       -> Ordering
    {
        let selfclass = self.classify();
        let otherclass = other.classify();

        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if selfclass==FpCategory::Zero && otherclass==FpCategory::Zero {
            return Ordering::Equal;
        }

        // Handle differing signs as a special case, even if they are very
        // close, most people consider them unequal.
        let self_pos = self.is_sign_positive();
        let other_pos = other.is_sign_positive();

        let udiff: i32 = match (self_pos, other_pos) {
            (true, false) => return Ordering::Greater,
            (false, true) => return Ordering::Less,
            (true, true) => self.ulps(other),
            (false, false) => other.ulps(self), // invert ulps for negatives
        };

        match udiff {
            x if x < -ulps => Ordering::Less,
            x if x >= -ulps && x <= ulps => Ordering::Equal,
            x if x > ulps => Ordering::Greater,
            _ => unreachable!()
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
    assert!(sum.approx_cmp_ulps(&product,1) == Ordering::Equal); // But should be close
    assert!(sum.approx_cmp_ulps(&product,0) != Ordering::Equal);
    assert!(product.approx_cmp_ulps(&sum,0) != Ordering::Equal);
}
#[test]
fn f32_approx_cmp_test2() {
    let x: f32 = 1000000_f32;
    let y: f32 = 1000000.1_f32;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_cmp_ulps(&y,2) == Ordering::Equal);
    assert!(x.approx_cmp_ulps(&y,1) == Ordering::Less);
    assert!(y.approx_cmp_ulps(&x,1) == Ordering::Greater);
}
#[test]
fn f32_approx_cmp_negatives() {
    let x: f32 = -1.0;
    let y: f32 = -2.0;
    assert!(x.approx_cmp_ulps(&y, 2) == Ordering::Greater);
}

// In all cases, approx_cmp() should be the same as cmp() if ulps=0
#[test]
fn f32_approx_cmp_vs_partial_cmp() {
    use std::mem;

    let testcases: [u32; 20] = [
        0,          // +0
        0x80000000, // -0
        0x00000101, // + denormal
        0x80000101, // - denormal
        0x00001101, // + denormal
        0x80001101, // - denormal
        0x01000101, // + normal
        0x81000101, // - normal
        0x01001101, // + normal
        0x81001101, // - normal
        0x7F800000, // +infinity
        0xFF800000, // -infinity
        0x7F801101, // SNaN
        0xFF801101, // SNaN
        0x7FC01101, // QNaN
        0xFFC01101, // QNaN
        0x7F801110, // SNaN
        0xFF801110, // SNaN
        0x7FC01110, // QNaN
        0xFFC01110, // QNaN

    ];

    let mut xf: f32;
    let mut yf: f32;
    for xbits in testcases.iter() {
        for ybits in testcases.iter() {
            xf = unsafe { mem::transmute::<u32,f32>(*xbits) };
            yf = unsafe { mem::transmute::<u32,f32>(*ybits) };
            if let Some(ordering) = xf.partial_cmp(&yf) {
                if ordering != xf.approx_cmp_ulps(&yf, 0) {
                    panic!("{} ({:x}) vs {} ({:x}): partial_cmp gives {:?} \
                            approx_cmp_ulps gives {:?}",
                           xf, xbits, yf, ybits, ordering , xf.approx_cmp_ulps(&yf, 0));
                }
            }
        }
        print!(".");
    }
}

impl ApproxOrdUlps for f64 {
    fn approx_cmp_ulps(&self, other: &f64, ulps: <<Self as ApproxEqUlps>::Flt as Ulps>::U)
                       -> Ordering
    {
        let selfclass = self.classify();
        let otherclass = other.classify();

        // -0 and +0 are drastically far in ulps terms, so
        // we need a special case for that.
        if selfclass==FpCategory::Zero && otherclass==FpCategory::Zero {
            return Ordering::Equal;
        }

        // Handle differing signs as a special case, even if they are very
        // close, most people consider them unequal.
        let self_pos = self.is_sign_positive();
        let other_pos = other.is_sign_positive();

        let udiff: i64 = match (self_pos, other_pos) {
            (true, false) => return Ordering::Greater,
            (false, true) => return Ordering::Less,
            (true, true) => self.ulps(other),
            (false, false) => other.ulps(self), // invert ulps for negatives
        };

        match udiff {
            x if x < -ulps => Ordering::Less,
            x if x >= -ulps && x <= ulps => Ordering::Equal,
            x if x > ulps => Ordering::Greater,
            _ => unreachable!()
        }
    }
}

#[test]
fn f64_approx_cmp_ulps_test1() {
    let f: f64 = 0.000000001_f64;
    let mut sum: f64 = 0.0_f64;
    for _ in 0_isize..10_isize { sum += f; }
    let product: f64 = f * 10.0_f64;
    assert!(sum != product); // Should not be directly equal:
    println!("Ulps Difference: {}",sum.ulps(&product));
    assert!(sum.approx_cmp_ulps(&product,1) == Ordering::Equal); // But should be close
    assert!(sum.approx_cmp_ulps(&product,0) != Ordering::Equal);
    assert!(product.approx_cmp_ulps(&sum,0) != Ordering::Equal);
}
#[test]
fn f64_approx_cmp_ulps_test2() {
    let x: f64 = 1000000_f64;
    let y: f64 = 1000000.0000000003_f64;
    assert!(x != y); // Should not be directly equal
    println!("Ulps Difference: {}",x.ulps(&y));
    assert!(x.approx_cmp_ulps(&y,3) == Ordering::Equal);
    assert!(x.approx_cmp_ulps(&y,2) == Ordering::Less);
    assert!(y.approx_cmp_ulps(&x,2) == Ordering::Greater);
}
#[test]
fn f64_approx_cmp_ulps_negatives() {
    let x: f64 = -1.0;
    let y: f64 = -2.0;
    assert!(x.approx_cmp_ulps(&y, 2) == Ordering::Greater);
}

// In all cases, approx_cmp_ulps() should be the same as cmp() if ulps=0
#[test]
fn f64_approx_cmp_ulps_vs_partial_cmp() {
    use std::mem;

    let testcases: [u64; 20] = [
        0,                   // +0
        0x80000000_00000000, // -0
        0x00000010_10000000, // + denormal
        0x80000010_10000000, // - denormal
        0x00000110_10000000, // + denormal
        0x80000110_10000000, // - denormal
        0x01000101_00100100, // + normal
        0x81000101_00100100, // - normal
        0x01001101_00100100, // + normal
        0x81001101_00100100, // - normal
        0x7FF00000_00000000, // +infinity
        0xFFF00000_00000000, // -infinity
        0x7FF01101_00100100, // SNaN
        0xFFF01101_00100100, // SNaN
        0x7FF81101_00100100, // QNaN
        0xFFF81101_00100100, // QNaN
        0x7FF01110_00100100, // SNaN
        0xFFF01110_00100100, // SNaN
        0x7FF81110_00100100, // QNaN
        0xFFF81110_00100100, // QNaN
    ];

    let mut xf: f64;
    let mut yf: f64;
    for xbits in testcases.iter() {
        for ybits in testcases.iter() {
            xf = unsafe { mem::transmute::<u64,f64>(*xbits) };
            yf = unsafe { mem::transmute::<u64,f64>(*ybits) };
            if let Some(ordering) = xf.partial_cmp(&yf) {
                if ordering != xf.approx_cmp_ulps(&yf, 0) {
                    panic!("{} ({:x}) vs {} ({:x}): partial_cmp gives {:?} \
                            approx_cmp_ulps gives {:?}",
                           xf, xbits, yf, ybits, ordering , xf.approx_cmp_ulps(&yf, 0));
                }
            }
        }
        print!(".");
    }
}
