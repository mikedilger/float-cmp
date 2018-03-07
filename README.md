# float-cmp

[![Build Status](https://travis-ci.org/mikedilger/float-cmp.svg?branch=master)](https://travis-ci.org/mikedilger/float-cmp)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)

Documentation is available at https://mikedilger.github.io/float-cmp


float-cmp defines traits for approximate comparison of floating point types which have fallen
away from exact equality due to the limited precision available within floating point
representations. Implementations of these traits are provided for `f32` and `f64` types.

The recommended go-to solution (although it may not be appropriate in all cases) is the
`approx_eq()` function in the `ApproxEq` trait.  An epsilon test is performed first, which
handles very small numbers, zeroes, and differing signs of very small numbers, considering
them equal if the difference is less than the given epsilon (e.g. f32::EPSILON). For larger
numbers, floating point representations are spaced further apart, and in these cases the ulps
test comes to the rescue. Numbers are considered equal if the number of floating point
representations between them is below a specified bound (Ulps are a cardinal count of
floating point representations that separate two floating point numbers).

Several other traits are provided including `Ulps`, `ApproxEqUlps`, `ApproxOrdUlps`, and
`ApproxEqRatio`.

## The problem

Floating point operations must round answers to the nearest representable number. Multiple
operations may result in an answer different from what you expect. In the following example,
the assert will fail, even though the printed output says "0.45 == 0.45":

```rust
  let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
  let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
  println!("{} == {}", a, b);
  assert!(a==b)  // Fails, because they are not exactly equal
```

This fails because the correct answer to most operations isn't exactly representable, and so
your computer's processor chooses to represent the answer with the closest value it has
available. This introduces error, and this error can accumulate as multiple operations are
performed.

## The solution

With `ApproxEq`, we can get the answer we intend:

```rust
  let a = 0.15_f32 + 0.15_f32 + 0.15_f32;
  let b = 0.1_f32 + 0.1_f32 + 0.25_f32;
  println!("{} == {}", a, b);
  assert!(a.approx_eq(&b, 2.0 * ::std::f32::EPSILON, 2)) // They are equal, within 2 ulps
```

I recommend you use a small integer for the `ulps` parameter (2 to 10 or so), and a
similar small multiple of the floating point's EPSILON constant (2.0 to 10.0 or so),
but please send feedback if you think you have better advice.

## Some explanation

We use the term ULP (units of least precision, or units in the last place) to mean the
difference between two adjacent floating point representations (adjacent meaning that there is
no floating point number between them). This term is borrowed from prior work (personally I
would have chosen "quanta"). The size of an ULP (measured as a float) varies
depending on the exponents of the floating point numbers in question. That is a good thing,
because as numbers fall away from equality due to the imprecise nature of their representation,
they fall away in ULPs terms, not in absolute terms.  Pure epsilon-based comparisons are
absolute and thus don't map well to the nature of the additive error issue. They work fine
for many ranges of numbers, but not for others (consider comparing -0.0000000028
to +0.00000097).

## Implementing these traits

You can implement `ApproxEq` for your own complex types. The trait and type parameter
notation can be a bit tricky, especially if your type is type parameterized around
floating point types.  So here is an example (you'll probably not specify the Copy trait
directly, but use some other NumTraits type floating point trait):

```rust
use float_cmp::{Ulps, ApproxEq};

pub struct Vec2<F> {
  pub x: F,
  pub y: F,
}

impl<F: Ulps + ApproxEq<Flt=F> + Copy> ApproxEq for Vec2<F> {
  type Flt = F;

  fn approx_eq(&self, other: &Self,
               epsilon: <F as ApproxEq>::Flt,
               ulps: <<F as ApproxEq>::Flt as Ulps>::U) -> bool
  {
    self.x.approx_eq(&other.x, epsilon, ulps)
      && self.y.approx_eq(&other.y, epsilon, ulps)
  }
}
```

## Inspiration

This crate was inspired by this Random ASCII blog post:

[https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/](https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/)
