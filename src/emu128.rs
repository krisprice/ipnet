//! An emulated 128 bit unsigned integer.
//!
//! This module provides `Emu128`, a 128 bit unsigned integer that is
//! emulated using two `u64` types. This is useful for operations on
//! IPv6 address, which are 128 bit unsigned integers.

use std::fmt;
use std::net::Ipv6Addr;
use std::ops::{BitAnd, BitOr, Shr, Shl};

/// An emulated 128 bit unsigned integer.
///
/// This module provides `Emu128`, a 128 bit unsigned integer that is
/// emulated using two `u64` types. This is useful for operations on
/// IPv6 address, which are 128 bit unsigned integers.
///
/// Currently `Emu128` only implements those operations that are useful
/// for the `Ipv6Net` type. It is not intended to become a full `u128`
/// implementation.
///
/// Conversion between `Ipv6Addr` and `Emu128` is provided by a `From`
/// and `Into` implementation on `Emu128`. The `into()` method must be
/// used to convert from an `Ipv6Addr` to an `Emu128` because it is not
/// possible to implement `From<Emu128> for Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use ipnet::Emu128;
///
/// let i1 = Emu128::from(1); // convert from u32
/// let i2 = Emu128::from([1, 1]); // convert from [u64; 2]
/// let slice: [u64; 2] = i2.into(); // convert into [u64; 2]
///
/// let a1: Ipv6Addr = "fd00::1".parse().unwrap();
/// let u1 = Emu128 { hi: 0xfd00_0000_0000_0000, lo: 1 };
/// let a2: Ipv6Addr = u1.into();
/// let u2: Emu128 = a1.into();
///
/// assert_eq!(a1, a2);
/// assert_eq!(u1, u2);
/// assert_eq!(u1, Emu128::from(a1));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Emu128 {
    pub hi: u64,
    pub lo: u64,
}

impl Emu128 {
    pub fn min_value() -> Emu128 {
        Emu128 { hi: 0, lo: 0 }
    }

    pub fn max_value() -> Emu128 {
        Emu128 { hi: u64::max_value(), lo: u64::max_value() }
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

    pub fn checked_shl(self, rhs: u8) -> Option<Self> {
        if rhs < 128 { Some(self << rhs) }
        else { None }
    }
    
    pub fn checked_shr(self, rhs: u8) -> Option<Self> {
        if rhs < 128 { Some(self >> rhs) } 
        else { None }
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
        if rhs == 0 {
            return self;
        }

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
        if rhs == 0 {
            return self;
        }
        
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

impl From<u32> for Emu128 {
    fn from(u: u32) -> Self {
        Emu128 {
            hi: 0,
            lo: u as u64,
        }
    }
}

impl From<[u64; 2]> for Emu128 {
    fn from(slice: [u64; 2]) -> Self {
        Emu128 {
            hi: slice[0],
            lo: slice[1],
        }
    }
}

impl From<Emu128> for [u64; 2] {
    fn from(u: Emu128) -> Self {
        [u.hi, u.lo]
    }
}

impl From<Ipv6Addr> for Emu128 {
    fn from(ip: Ipv6Addr) -> Self {
        let ip = ip.octets();
        Emu128 {
            hi: ((ip[0] as u64) << 56) + ((ip[1] as u64) << 48) +
                ((ip[2] as u64) << 40) + ((ip[3] as u64) << 32) +
                ((ip[4] as u64) << 24) + ((ip[5] as u64) << 16) +
                ((ip[6] as u64) << 8) + (ip[7] as u64),
            lo: ((ip[8] as u64) << 56) + ((ip[9] as u64) << 48) +
                ((ip[10] as u64) << 40) + ((ip[11] as u64) << 32) +
                ((ip[12] as u64) << 24) + ((ip[13] as u64) << 16) +
                ((ip[14] as u64) << 8) + (ip[15] as u64),
        }
    }
}

impl Into<Ipv6Addr> for Emu128 {
    fn into(self) -> Ipv6Addr {
        Ipv6Addr::new(
            (self.hi >> 48) as u16, (self.hi >> 32) as u16, (self.hi >> 16) as u16, self.hi as u16,
            (self.lo >> 48) as u16, (self.lo >> 32) as u16, (self.lo >> 16) as u16, self.lo as u16,
        )    
    }
}

impl fmt::Display for Emu128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "({}, {})", self.hi, self.lo)
    }
}

#[cfg(test)]
mod tests {
    use std::u64;
    use super::*;

    #[test]
    fn test_emu128_from() {
        assert_eq!(Emu128::from(123), Emu128 { hi: 0, lo: 123 });
        assert_eq!(Emu128::from([123, 123]), Emu128 { hi: 123, lo: 123 });
        let slice: [u64; 2] = (Emu128 { hi: 123, lo: 123 }).into();
        assert_eq!(slice, [123u64, 123u64]);
    }

    #[test]
    fn test_emu128_min_max_value() {
        assert_eq!(Emu128::min_value(), Emu128 { hi: 0, lo: 0 });
        assert_eq!(Emu128::max_value(), Emu128 { hi: u64::MAX, lo: u64::MAX });
    }

    #[test]
    #[should_panic]
    fn test_emu128_shl_overflow() {
        Emu128::max_value() << 128;
    }

    #[test]
    #[should_panic]
    fn test_emu128_shr_overflow() {
        Emu128::max_value() >> 128;
    }

    #[test]
    fn test_emu128_shl_shr() {
        let i = Emu128::from([1, 1]);
        let j = Emu128::from([1 << 63, 1 << 63]);
        
        assert_eq!(i << 0, i);
        assert_eq!(i << 1, Emu128 { hi: 2, lo: 2 });
        assert_eq!(i << 63, Emu128 { hi: 1 << 63, lo: 1 << 63 });
        assert_eq!(i << 64, Emu128 { hi: 1, lo: 0 });
        assert_eq!(i << 127, Emu128 { hi: 1 << 63, lo: 0 });
        assert_eq!(j >> 0, j);
        assert_eq!(j >> 1, Emu128 { hi: 1 << 62, lo: 1 << 62 });
        assert_eq!(j >> 63, Emu128 { hi: 1, lo: 1 });
        assert_eq!(j >> 64, Emu128 { hi: 0, lo: 1 << 63 });
        assert_eq!(j >> 127, Emu128 { hi: 0, lo: 1 });
    }

    #[test]
    fn test_emu128_and_or() {
        let i0 = Emu128::min_value();
        let i1 = Emu128::from([1, 1]);
        let i3 = Emu128::from([3, 3]);
        let im = Emu128::max_value();
        
        assert_eq!(i0 & i3, i0);
        assert_eq!(i1 & i3, i1);
        assert_eq!(i1 & im, i1);
        assert_eq!(i0 | i1, i1);
        assert_eq!(i0 | i3, i3);
        assert_eq!(i1 | i3, Emu128 { hi: 3, lo: 3 });
        assert_eq!(i0 | im, Emu128::max_value());
    }

    #[test]
    fn test_emu128_add_sub() {
        let i1 = Emu128::from([1, 1]);
        let i3 = Emu128::from([3, 3]);
        let im = Emu128::from([0, u64::MAX]);
        let mm = Emu128::max_value();
        
        assert_eq!(i1.saturating_add(i1), Emu128 { hi: 2, lo: 2 });
        assert_eq!(i1.saturating_add(i3), Emu128 { hi: 4, lo: 4 });
        assert_eq!(im.saturating_add(i1), Emu128 { hi: 2, lo: 0 });
        assert_eq!(im.saturating_add(i3), Emu128 { hi: 4, lo: 2 });
        assert_eq!(im.saturating_add(i1), Emu128 { hi: 2, lo: 0 });
        assert_eq!(mm.saturating_add(i1), Emu128::max_value());

        assert_eq!(i1.saturating_sub(mm), Emu128::min_value());
        assert_eq!(i1.saturating_sub(im), Emu128 { hi: 0, lo: 2 });
        assert_eq!(mm.saturating_sub(i1), Emu128 { hi: u64::MAX-1, lo: u64::MAX-1 });
        assert_eq!(mm.saturating_sub(im), Emu128 { hi: u64::MAX, lo: 0 });
    }
}
