//! An emulated 128 bit unsigned integer.
//!
//! This module provides [`Emu128`], a 128 bit unsigned integer that is
//! emulated using two `u64` types. This is useful for operations on
//! IPv6 address, which are 128 bit unsigned integers.
//!
//! Currently `Emu128` only implements those operations that are useful
//! for the `Ipv6Net` type. It is not intended to become a full `u128`
//! implementation.
//!
//! [`Emu128`]: struct.Emu128.html

use std;
use std::ops::{BitAnd, BitOr, Shr, Shl};

/// An emulated 128 bit unsigned integer.
///
/// This module provides [`Emu128`], a 128 bit unsigned integer that is
/// emulated using two `u64` types. This is useful for operations on
/// IPv6 address, which are 128 bit unsigned integers.
///
/// Currently `Emu128` only implements those operations that are useful
/// for the `Ipv6Net` type. It is not intended to become a full `u128`
/// implementation.
///
/// # Examples
///
/// ```
/// use std::u64;
/// use ipnet::Emu128;
///
/// let i0 = Emu128::min_value();
/// let i1 = Emu128::from([1, 1]);
/// let i2 = Emu128::max_value();
/// let i3 = Emu128::from([1, u64::MAX]);
///
/// assert_eq!(i0, Emu128 { hi: 0, lo: 0 });
/// assert_eq!(i2, Emu128 { hi: std::u64::MAX, lo: std::u64::MAX });
/// assert_eq!(i0.saturating_sub(i2), Emu128::min_value());
/// assert_eq!(i2.saturating_add(i2), Emu128::max_value());
/// assert_eq!(i1.saturating_add(i1), Emu128 { hi: 2, lo: 2 });
/// assert_eq!(i2.saturating_sub(i1), Emu128 { hi: std::u64::MAX-1, lo: std::u64::MAX-1 });
/// assert_eq!(i3.saturating_add(i1), Emu128 { hi: 3, lo: 0 });
/// assert_eq!(i3.saturating_sub(i1), Emu128 { hi: 0, lo: std::u64::MAX-1 });
/// assert_eq!(i1 << 1, Emu128 { hi: 2, lo: 2 });
/// assert_eq!(i1 << 63, Emu128 { hi: 1 << 63, lo: 1 << 63 });
/// assert_eq!(i1 << 127, Emu128 { hi: 1 << 63, lo: 0 });
/// assert_eq!(i1 >> 1, Emu128 { hi: 0, lo: 1u64 << 63 });
/// assert_eq!(i1 >> 63, Emu128 { hi: 0, lo: 2 });
/// assert_eq!(i1 >> 127, Emu128 { hi: 0, lo: 0 });
/// assert_eq!(i0 | i1, Emu128 { hi: 1, lo: 1 });
/// assert_eq!(i1 & i1, Emu128 { hi: 1, lo: 1 });
/// assert_eq!(i1 & i3, Emu128 { hi: 1, lo: 1 });
/// assert_eq!(i1 | i3, Emu128 { hi: 1, lo: std::u64::MAX });
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Emu128 {
    pub hi: u64,
    pub lo: u64,
}

impl Emu128 {
    pub fn min_value() -> Emu128 {
        Emu128 { hi: 0, lo: 0 }
    }

    pub fn max_value() -> Emu128 {
        Emu128 { hi: std::u64::MAX, lo: std::u64::MAX }
    }

    pub fn saturating_add(self, other: Emu128) -> Emu128 {
        let (lo, ov) = self.lo.overflowing_add(other.lo);
        let res = self.hi.checked_add(other.hi).and_then(|x| x.checked_add(if ov { 1 } else { 0 }));
        match res {
            Some(hi) => Emu128 { hi: hi, lo: lo },
            None => Emu128::max_value(),
        }
    }

    pub fn saturating_sub(self, other: Emu128) -> Emu128 {
        let (lo, ov) = self.lo.overflowing_sub(other.lo);
        let res = self.hi.checked_sub(other.hi).and_then(|x| x.checked_sub(if ov { 1 } else { 0 }));
        match res {
            Some(hi) => Emu128 { hi: hi, lo: lo },
            None => Emu128::min_value(),
        }
    }

    pub fn leading_zeros(self) -> u32 {
        if self.hi > 0 { self.hi.leading_zeros() } else { self.lo.leading_zeros() + 64 } 
    }

    pub fn trailing_zeros(self) -> u32 {
        if self.lo > 0 { self.lo.trailing_zeros() } else { self.hi.trailing_zeros() + 64 } 
    }
}

impl Shl<u8> for Emu128 {
    type Output = Self;

    fn shl(self, rhs: u8) -> Emu128 {
        if rhs < 64 {
            Emu128 {
                hi: self.hi << rhs | self.lo >> (64-rhs),
                lo: self.lo << rhs
            }
        }
        else {
            Emu128 {
                hi: self.lo << (rhs-64),
                lo: 0
            }
        }
    }
}

impl Shr<u8> for Emu128 {
    type Output = Self;

    fn shr(self, rhs: u8) -> Emu128 {
        if rhs < 64 {
            Emu128 {
                hi: self.hi >> rhs,
                lo: self.lo >> rhs | self.hi << (64-rhs),
            }
        }
        else {
            Emu128 {
                hi: 0,
                lo: self.hi >> (rhs-64),
            }
        }
    }
}

impl BitAnd for Emu128 {
    type Output = Self;
    fn bitand(self, rhs: Emu128) -> Emu128 {
        Emu128 {
            hi: self.hi & rhs.hi,
            lo: self.lo & rhs.lo,
        }
    }
}

impl BitOr for Emu128 {
    type Output = Self;
    fn bitor(self, rhs: Emu128) -> Emu128 {
        Emu128 {
            hi: self.hi | rhs.hi,
            lo: self.lo | rhs.lo,
        }
    }
}

/// Convert an a `[u64; 2]` slice into an `Emu128`.
///
/// # Examples
///
/// ```
/// use ipnet::Emu128;
///
/// let u = Emu128::from([123u64, 123u64]);
/// let v: [u64; 2] = u.into();
/// assert_eq!(v, [123u64, 123u64]);
/// ```
impl From<[u64; 2]> for Emu128 {
    fn from(slice: [u64; 2]) -> Self {
        Emu128 {
            hi: slice[0],
            lo: slice[1],
        }
    }
}

/// Convert an Emu128 into a `[u64; 2]` slice.
///
/// # Examples
///
/// ```
/// use ipnet::Emu128;
///
/// let u = Emu128::from([123u64, 123u64]);
/// let v: [u64; 2] = u.into();
/// assert_eq!(v, [123u64, 123u64]);
/// ```
impl From<Emu128> for [u64; 2] {
    fn from(u: Emu128) -> Self {
        [u.hi, u.lo]
    }
}
