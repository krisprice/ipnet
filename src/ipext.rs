//! Extensions to the standard IP address types for common operations.
//!
//! The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//! the `Ipv4Addr` and `Ipv6Addr` types to provide their respective
//! operations.
//!
//! # TODO:
//!
//! * Can we implement the `std::ops::{Add, Sub, BitAnd, BitOr}` traits
//!   for `Ipv4Addr` and `Ipv6Addr` in the standard library? These are
//!   common operations on IP addresses.
//!
//! * Tests and documentation.

use std::net::{Ipv4Addr, Ipv6Addr};
use emu128::emu128;

/// Convert an `Ipv6Addr` into an `emu128`.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::Emu128;
///
/// let a = Ipv6Addr::from_str("fd00::1").unwrap();
/// let u = Emu128 { hi: 0xfd00_0000_0000_0000, lo: 1 };
/// let a2: Ipv6Addr = u.into();
///
/// assert_eq!(a, a2);
/// assert_eq!(u, a.into());
/// assert_eq!(u, Emu128::from(a));
/// ```
impl From<Ipv6Addr> for emu128 {
    fn from(ip: Ipv6Addr) -> Self {
        let ip = ip.octets();
        emu128 {
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

/// Convert an `emu128` into an `Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::Emu128;
///
/// let a = Ipv6Addr::from_str("fd00::1").unwrap();
/// let u = Emu128 { hi: 0xfd00_0000_0000_0000, lo: 1 };
/// let a2: Ipv6Addr = u.into();
///
/// assert_eq!(a, a2);
/// assert_eq!(u, a.into());
/// assert_eq!(u, Emu128::from(a));
/// ```
impl Into<Ipv6Addr> for emu128 {
    fn into(self) -> Ipv6Addr {
        Ipv6Addr::new(
            (self.hi >> 48) as u16, (self.hi >> 32) as u16, (self.hi >> 16) as u16, self.hi as u16,
            (self.lo >> 48) as u16, (self.lo >> 32) as u16, (self.lo >> 16) as u16, self.lo as u16,
        )    
    }
}

/*pub fn ipv6_addr_from_emu128(ip: emu128) -> Ipv6Addr {
    Ipv6Addr::new(
        (ip.hi >> 48) as u16, (ip.hi >> 32) as u16, (ip.hi >> 16) as u16, ip.hi as u16,
        (ip.lo >> 48) as u16, (ip.lo >> 32) as u16, (ip.lo >> 16) as u16, ip.lo as u16
    )
}

pub fn ipv6_addr_into_emu128(ip: Ipv6Addr) -> emu128 {
    let ip = ip.octets();
    emu128 {
        hi: ((ip[0] as u64) << 56) + ((ip[1] as u64) << 48) +
            ((ip[2] as u64) << 40) + ((ip[3] as u64) << 32) +
            ((ip[4] as u64) << 24) + ((ip[5] as u64) << 16) +
            ((ip[6] as u64) << 8) + (ip[7] as u64),
        lo: ((ip[8] as u64) << 56) + ((ip[9] as u64) << 48) +
            ((ip[10] as u64) << 40) + ((ip[11] as u64) << 32) +
            ((ip[12] as u64) << 24) + ((ip[13] as u64) << 16) +
            ((ip[14] as u64) << 8) + (ip[15] as u64),
    }
}*/

pub trait IpAdd<RHS = Self> {
    type Output;
    fn saturating_add(self, rhs: RHS) -> Self::Output;
}

pub trait IpSub<RHS = Self> {
    type Output;
    fn sub(self, rhs: RHS) -> Self::Output;
}

pub trait IpBitAnd<RHS = Self> {
    type Output;
    fn bitand(self, rhs: RHS) -> Self::Output;
}

pub trait IpBitOr<RHS = Self> {
    type Output;
    fn bitor(self, rhs: RHS) -> Self::Output;
}

macro_rules! ip_add_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpAdd<$f> for $t {
            type Output = $t;
            #[inline]
            fn saturating_add(self, rhs: $f) -> $t {
                Self::from(u32::from(self).saturating_add(u32::from(rhs)))
            }
        }
    )*
    }
}

ip_add_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_sub_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpSub<$f> for $t {
            type Output = $t;
            #[inline]
            fn sub(self, rhs: $f) -> $t {
                Self::from(u32::from(self).saturating_sub(u32::from(rhs)))
            }
        }
    )*
    }
}

ip_sub_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_bitand_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitAnd<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitand(self, rhs: $f) -> $t {
                Self::from(u32::from(self) & u32::from(rhs))
            }
        }
    )*
    }
}

ip_bitand_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_bitor_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitOr<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitor(self, rhs: $f) -> $t {
                Self::from(u32::from(self) | u32::from(rhs))
            }
        }
    )*
    }
}

ip_bitor_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

impl IpBitAnd<emu128> for Ipv6Addr {
    type Output = Ipv6Addr;
    #[inline]
    fn bitand(self, rhs: emu128) -> Ipv6Addr {
        emu128::into(emu128::from(self) & rhs)
    }
}

impl IpBitOr<emu128> for Ipv6Addr {
    type Output = Ipv6Addr;
    #[inline]
    fn bitor(self, rhs: emu128) -> Ipv6Addr {
        emu128::into(emu128::from(self) | rhs)
    }
}
