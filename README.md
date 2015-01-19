# float-cmp
float-cmp defines traits for approximate floating point comparison, including
ApproxEq, ApproxOrd, and Ulps, where the caller specifies the number of adjacent
floating point representations (called `ulps`) that are allowed between two
comparands which are to be considered equal if they are within that distance of
each other.
