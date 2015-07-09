# float-cmp

[![Build Status](https://travis-ci.org/mikedilger/float-cmp.svg?branch=master)](https://travis-ci.org/mikedilger/float-cmp)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)

Documentation is available at https://mikedilger.github.io/float-cmp

float-cmp defines traits for approximate comparison of floating point types which have fallen away
from exact equality due to rounding and inaccuracies within the floating point unit of your
computer's processor. Implementations of these traits are provided for `f32` and `f64` types.

Two methods of comparison are provided. The first, `ApproxEqUlps` and `ApproxOrdUlps`, consider two
comparands equal if the number of representable floating point numbers between them is below a
specified bound. This works well in most cases.

The second method of comparison, `ApproxEqRatio`, considers two comparands equal if the ratio of the
difference between them to the larger is below some specified bound.  This handles many of the cases
that the former type of comparison doesn't handle well.

To help choose which comparison method to use, and to learn many suprising facts and oddities about
floating point numbers, please refer to the following excellent website:
https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/
