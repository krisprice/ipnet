//! Provides left and right shift methods that check the RHS is less
//! than the bit width of the LHS, and returns zero if not. This avoids
//! a panic as Rust doesn't permit overflowing shifts.
//!
//! Does not support negative right hand sides. This is fine for my uses.
//! If a negative use used it will panic at runtime. It's an easy change
//! below to fix this if needed.

use emu128::Emu128;

/// Provides a `saturating_shl()` method that avoids a panic if the RHS
/// is not less than the bit width.
pub trait SaturatingShl<RHS> {
    type Output;
    fn saturating_shl(self, rhs: RHS) -> Self::Output;
}

/// Provides a `saturating_shr()` method that avoids a panic if the RHS
/// is not less than the bit width.
pub trait SaturatingShr<RHS> {
    type Output;
    fn saturating_shr(self, rhs: RHS) -> Self::Output;
}

macro_rules! saturating_shl_shr_impl {
    ($t:ty, $u:ty, $w:expr, $z:expr) => (
        impl SaturatingShl<$u> for $t {
            type Output = $t;

            #[inline]
            fn saturating_shl(self, rhs: $u) -> $t {
                if rhs < $w { self << rhs } else { $z }
            }
        }

        impl SaturatingShr<$u> for $t {
            type Output = $t;

            #[inline]
            fn saturating_shr(self, rhs: $u) -> $t {
                if rhs < $w { self >> rhs } else { $z }
            }
        }
    )
}

saturating_shl_shr_impl!(u32, u8, 32, 0);
saturating_shl_shr_impl!(u64, u8, 64, 0);
saturating_shl_shr_impl!(Emu128, u8, 128, Emu128::min_value());

#[cfg(test)]
mod tests {
    use super::*;
    
    macro_rules! saturating_shl_shr_test {
        ($name:ident, $w:expr, $min:expr, $max:expr) => (
            #[test]
            fn $name() {
                assert_eq!($max.saturating_shl(0), $max);
                assert_eq!($max.saturating_shl($w-1), $max << $w-1);
                assert_eq!($max.saturating_shl($w), $min);
                assert_eq!($max.saturating_shr(0), $max);
                assert_eq!($max.saturating_shr($w-1), $max >> $w-1);
                assert_eq!($max.saturating_shr($w), $min);
            }
        )
    }

    saturating_shl_shr_test!(test_saturating_shl_u32, 32, ::std::u32::MIN, ::std::u32::MAX);
    saturating_shl_shr_test!(test_saturating_shl_u64, 64, ::std::u64::MIN, ::std::u64::MAX);
    saturating_shl_shr_test!(test_saturating_shl_emu128, 128, Emu128::min_value(), Emu128::max_value());
}
