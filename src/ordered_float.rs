use ordered_float::OrderedFloat;
use crate::{ApproxEq, ApproxEqUlps, Ulps};
use crate::{F32Margin, F64Margin};

impl ApproxEq for OrderedFloat<f32> {
    type Margin = F32Margin;

    fn approx_eq<M: Into<Self::Margin>>(self, other: OrderedFloat<f32>, margin: M) -> bool {
        let margin = margin.into();
        self.0.approx_eq(other.0, margin)
    }
}

impl ApproxEq for OrderedFloat<f64> {
    type Margin = F64Margin;

    fn approx_eq<M: Into<Self::Margin>>(self, other: OrderedFloat<f64>, margin: M) -> bool {
        let margin = margin.into();
        self.0.approx_eq(other.0, margin)
    }
}

impl Ulps for OrderedFloat<f32> {
    type U = i32;

    fn ulps(&self, other: &OrderedFloat<f32>) -> i32 {
        self.0.ulps(&other.0)
    }

    fn next(&self) -> Self {
        OrderedFloat(self.0.next())
    }

    fn prev(&self) -> Self {
        OrderedFloat(self.0.next())
    }
}

impl Ulps for OrderedFloat<f64> {
    type U = i64;

    fn ulps(&self, other: &OrderedFloat<f64>) -> i64 {
        self.0.ulps(&other.0)
    }

    fn next(&self) -> Self {
        OrderedFloat(self.0.next())
    }

    fn prev(&self) -> Self {
        OrderedFloat(self.0.next())
    }
}

impl ApproxEqUlps for OrderedFloat<f32> {
    type Flt = f32;

    fn approx_eq_ulps(&self, other: &OrderedFloat<f32>, ulps: i32) -> bool {
        self.0.approx_eq_ulps(&other.0, ulps)
    }
}

impl ApproxEqUlps for OrderedFloat<f64> {
    type Flt = f64;

    fn approx_eq_ulps(&self, other: &OrderedFloat<f64>, ulps: i64) -> bool {
        self.0.approx_eq_ulps(&other.0, ulps)
    }
}

#[cfg(feature = "ratio")]
use crate::ApproxEqRatio;

#[cfg(feature = "ratio")]
impl ApproxEqRatio for OrderedFloat<f32> {}

#[cfg(feature = "ratio")]
impl ApproxEqRatio for OrderedFloat<f64> {}
