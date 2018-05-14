
// approx_eq!(f32, 15.0, 15.1)

#[macro_export]
macro_rules! approx_eq {
    ($typ:ty, $lhs:expr, $rhs:expr) => {
        {
            let m: <$typ as ApproxEq>::Margin = Default::default();
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    ($typ:ty, $lhs:expr, $rhs:expr $(, $set:ident = $val:expr)*) => {
        {
            let m = <$typ as ApproxEq>::Margin::zero()$(.$set($val))*;
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    ($typ:ty, $lhs:expr, $rhs:expr, $marg:expr) => {
        {
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, $marg)
        }
    };

    /*
    (f32, $lhs:expr, $rhs:expr, ulps = $ulps:expr) => {
        {
            let m = F32Margin { epsilon: 0.0, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f32, $lhs:expr, $rhs:expr, epsilon = $epsilon:expr) => {
        {
            let m = F32Margin { epsilon: $epsilon, ulps: 0 };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f32, $lhs:expr, $rhs:expr, ulps = $ulps:expr, epsilon = $epsilon:expr) => {
        {
            let m = F32Margin { epsilon: $epsilon, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f32, $lhs:expr, $rhs:expr, epsilon = $epsilon:expr, ulps = $ulps:expr) => {
        {
            let m = F32Margin { epsilon: $epsilon, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f64, $lhs:expr, $rhs:expr, ulps = $ulps:expr) => {
        {
            let m = F64Margin { epsilon: 0.0, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f64, $lhs:expr, $rhs:expr, epsilon = $epsilon:expr) => {
        {
            let m = F64Margin { epsilon: $epsilon, ulps: 0 };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f64, $lhs:expr, $rhs:expr, ulps = $ulps:expr, epsilon = $epsilon:expr) => {
        {
            let m = F64Margin { epsilon: $epsilon, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
    (f64, $lhs:expr, $rhs:expr, epsilon = $epsilon:expr, ulps = $ulps:expr) => {
        {
            let m = F64Margin { epsilon: $epsilon, ulps: $ulps };
            <$typ as ApproxEq>::approx_eq($lhs, $rhs, m)
        }
    };
*/
}
