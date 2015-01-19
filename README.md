# float-cmp

[![Build Status](https://travis-ci.org/mikedilger/float-cmp.svg?branch=master)](https://travis-ci.org/mikedilger/float-cmp)

Documentation is available at https://mikedilger.github.io/float-cmp

float-cmp defines traits for approximate floating point comparison, including
ApproxEq, ApproxOrd, and Ulps, where the caller specifies the number of adjacent
floating point representations (called `ulps`) that are allowed between two
comparands which are to be considered equal if they are within that distance of
each other.

For more information about floating point comparison and many other suprising facts
and oddities about floating point numbers, please refer to the following excellent
website:  https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/
