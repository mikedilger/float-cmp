// Copyright 2014-2018 Optimal Computing (NZ) Ltd.
// Licensed under the MIT license.  See LICENSE for details.

use std::mem;
use num_traits::NumCast;

/// A trait for floating point numbers which computes the number of representable
/// values or ULPs (Units of Least Precision) that separate the two given values.
pub trait Ulps {
    type U: Copy + NumCast;

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
        let ai32: i32 = unsafe { mem::transmute::<f32,i32>(*self) };
        let bi32: i32 = unsafe { mem::transmute::<f32,i32>(*other) };

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

#[test]
fn f32_ulps_test5() {
    let x: f32 = 2.0;
    let ulps: i32 = unsafe { mem::transmute(x) };
    let x2: f32 = unsafe { mem::transmute(ulps) };
    assert_eq!(x, x2);
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
        let ai64: i64 = unsafe { mem::transmute::<f64,i64>(*self) };
        let bi64: i64 = unsafe { mem::transmute::<f64,i64>(*other) };

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

#[test]
fn f64_ulps_test5() {
    let x: f64 = 2.0;
    let ulps: i64 = unsafe { mem::transmute(x) };
    let x2: f64 = unsafe { mem::transmute(ulps) };
    assert_eq!(x, x2);
}
