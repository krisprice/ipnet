// TODO: Would it be possible to get something like this in Rust core?
//
// Does not support negative right hand sides. This is fine for my uses
// where I only need lhs=u64 and rhs=u8. But if implemented with RHS as
// an integer and a negative is supplied it will panic at runtime. Easy
// change to fix below if needed.

use emu128::Emu128;

pub trait SaturatingShl<RHS> {
    type Output;
    fn saturating_shl(self, rhs: RHS) -> Self::Output;
}

macro_rules! saturating_shl_impl {
    ($t:ty, $f:ty, $w:expr, $z:expr) => (
        impl SaturatingShl<$f> for $t {
            type Output = $t;

            #[inline]
            fn saturating_shl(self, rhs: $f) -> $t {
                if rhs < $w { self << rhs } else { $z }
            }
        }
    )
}

pub trait SaturatingShr<RHS> {
    type Output;
    fn saturating_shr(self, rhs: RHS) -> Self::Output;
}

macro_rules! saturating_shr_impl {
    ($t:ty, $f:ty, $w:expr, $z:expr) => (
        impl SaturatingShr<$f> for $t {
            type Output = $t;

            #[inline]
            fn saturating_shr(self, rhs: $f) -> $t {
                if rhs < $w { self >> rhs } else { $z }
            }
        }
    )
}

saturating_shl_impl!(u32, u8, 32, 0);
saturating_shr_impl!(u32, u8, 32, 0);
saturating_shl_impl!(u64, u8, 64, 0);
saturating_shr_impl!(u64, u8, 64, 0);
saturating_shl_impl!(Emu128, u8, 128, Emu128 { hi: 0, lo: 0 });
saturating_shr_impl!(Emu128, u8, 128, Emu128 { hi: 0, lo: 0 });

#[cfg(test)]
mod tests {
    use std::mem::size_of;
    use super::*;
    
    macro_rules! saturating_shl_tests {
        ($($name:ident: ($lhs:ty, $rhs:ty),)*) => {
        $(
            #[test]
            fn $name() {
                let a: $lhs = 0b1;
                let z: $rhs = 0;
                let w: $rhs = 8 * size_of::<$lhs>() as $rhs;
                assert_eq!(a.saturating_shl(z), a);
                assert_eq!(a.saturating_shl(w-1), a << w-1);
                assert_eq!(a.saturating_shl(w), 0);
                assert_eq!(a.saturating_shl(z.wrapping_sub(1)), 0);
            }
        )*
        }
    }
    
    macro_rules! saturating_shr_tests {
        ($($name:ident: ($lhs:ty, $rhs:ty),)*) => {
        $(
            #[test]
            fn $name() {
                let a: $lhs = 0b1;
                let z: $rhs = 0;
                let w: $rhs = 8 * size_of::<$lhs>() as $rhs;
                assert_eq!(a.saturating_shr(z), a);
                assert_eq!(a.saturating_shr(w-1), a >> w-1);
                assert_eq!(a.saturating_shr(w), 0);
                assert_eq!(a.saturating_shr(z.wrapping_sub(1)), 0);
            }
        )*
        }
    }

    saturating_shl_tests! {
        saturating_shl_u32_u8: (u32, u8),
        saturating_shl_u64_u8: (u64, u8),
    }

    saturating_shr_tests! {
        saturating_shr_u32_u8: (u32, u8),
        saturating_shr_u64_u8: (u64, u8),
    }
}
