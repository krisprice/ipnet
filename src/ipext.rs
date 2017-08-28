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

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use emu128::Emu128;

/// Convert an `Ipv6Addr` into an `Emu128`.
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

/// Convert an `Emu128` into an `Ipv6Addr`.
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
impl Into<Ipv6Addr> for Emu128 {
    fn into(self) -> Ipv6Addr {
        Ipv6Addr::new(
            (self.hi >> 48) as u16, (self.hi >> 32) as u16, (self.hi >> 16) as u16, self.hi as u16,
            (self.lo >> 48) as u16, (self.lo >> 32) as u16, (self.lo >> 16) as u16, self.lo as u16,
        )    
    }
}

/// An `Iterator` over a range of IPv4 or IPv6 addresses.
///
/// This might be deprecated and replaced with an implementation of
/// `Range` for IP addresses when `Range` and it's required traits are
/// stablized.
///
/// # Examples
///
/// ```
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
/// use std::str::FromStr;
/// use ipnet::{IpAddrIter, IpAdd};
///
/// let i = IpAddrIter::new(IpAddr::from_str("10.0.0.0").unwrap(), IpAddr::from_str("10.0.0.3").unwrap());
/// let i4 = IpAddrIter::new(Ipv4Addr::from_str("10.0.0.0").unwrap(), Ipv4Addr::from_str("10.0.0.3").unwrap());
/// let i6 = IpAddrIter::new(Ipv6Addr::from_str("fd00::").unwrap(), Ipv6Addr::from_str("fd00::3").unwrap());
///
/// let v = vec![
///     IpAddr::from_str("10.0.0.0").unwrap(),
///     IpAddr::from_str("10.0.0.1").unwrap(),
///     IpAddr::from_str("10.0.0.2").unwrap(),
///     IpAddr::from_str("10.0.0.3").unwrap(),
/// ];
/// let v4 = vec![
///     Ipv4Addr::from_str("10.0.0.0").unwrap(),
///     Ipv4Addr::from_str("10.0.0.1").unwrap(),
///     Ipv4Addr::from_str("10.0.0.2").unwrap(),
///     Ipv4Addr::from_str("10.0.0.3").unwrap(),
/// ];
/// let v6 = vec![
///     Ipv6Addr::from_str("fd00::").unwrap(),
///     Ipv6Addr::from_str("fd00::1").unwrap(),
///     Ipv6Addr::from_str("fd00::2").unwrap(),
///     Ipv6Addr::from_str("fd00::3").unwrap(),
/// ];
///
/// assert_eq!(i.collect::<Vec<IpAddr>>(), v);
/// assert_eq!(i4.collect::<Vec<Ipv4Addr>>(), v4);
/// assert_eq!(i6.collect::<Vec<Ipv6Addr>>(), v6);
/// ```
pub struct IpAddrIter<T> {
    pub start: T,
    pub end: T,
}

impl<T> IpAddrIter<T> {
    pub fn new(start: T, end: T) -> Self {
        IpAddrIter {
            start: start,
            end: end,
        }
    }
}

impl<T> Iterator for IpAddrIter<T>
    where T: Copy + PartialOrd + IpAdd<u32, Output=T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start > self.end {
            return None;
        }
        let res = Some(self.start);
        self.start = self.start.saturating_add(1);
        res
    }
}

/// Provides a `saturating_add()` method for `Ipv4Addr` and `Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::{Ipv4Addr, Ipv6Addr};
/// use std::str::FromStr;
/// use ipnet::{IpAdd, Emu128};
///
/// let ip0 = Ipv4Addr::from_str("0.0.0.0").unwrap();
/// let ip1 = Ipv4Addr::from_str("1.1.1.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("254.254.254.254").unwrap();
///
/// assert_eq!(ip1.saturating_add(ip0), Ipv4Addr::from_str("1.1.1.1").unwrap());
/// assert_eq!(ip1.saturating_add(ip1), Ipv4Addr::from_str("2.2.2.2").unwrap());
/// assert_eq!(u32::from(ip2.saturating_add(ip1)), u32::max_value());
/// assert_eq!(u32::from(ip2.saturating_add(ip2)), u32::max_value());
///
/// let ip60 = Ipv6Addr::from_str("::").unwrap();
/// let ip61 = Ipv6Addr::from_str("::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap();
///
/// assert_eq!(ip61.saturating_add(ip60), Ipv6Addr::from_str("::1").unwrap());
/// assert_eq!(ip61.saturating_add(ip61), Ipv6Addr::from_str("::2").unwrap());
/// assert_eq!(Emu128::from(ip62.saturating_add(ip61)), Emu128::max_value());
/// assert_eq!(Emu128::from(ip62.saturating_add(ip62)), Emu128::max_value());
/// ```
pub trait IpAdd<RHS = Self> {
    type Output;
    fn saturating_add(self, rhs: RHS) -> Self::Output;
}

/// Provides a `saturating_sub()` method for `Ipv4Addr` and `Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::{Ipv4Addr, Ipv6Addr};
/// use std::str::FromStr;
/// use ipnet::IpSub;
///
/// let ip0 = Ipv4Addr::from_str("0.0.0.0").unwrap();
/// let ip1 = Ipv4Addr::from_str("1.1.1.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("2.2.2.2").unwrap();
///
/// assert_eq!(ip0.saturating_sub(ip1), Ipv4Addr::from_str("0.0.0.0").unwrap());
/// assert_eq!(ip2.saturating_sub(ip1), Ipv4Addr::from_str("1.1.1.1").unwrap());
/// 
/// let ip60 = Ipv6Addr::from_str("::").unwrap();
/// let ip61 = Ipv6Addr::from_str("::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("::2").unwrap();
///
/// assert_eq!(ip60.saturating_sub(ip61), Ipv6Addr::from_str("::").unwrap());
/// assert_eq!(ip62.saturating_sub(ip61), Ipv6Addr::from_str("::1").unwrap());
/// ```
pub trait IpSub<RHS = Self> {
    type Output;
    fn saturating_sub(self, rhs: RHS) -> Self::Output;
}

/// Provides a `bitand()` method for `Ipv4Addr` and `Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::{Ipv4Addr, Ipv6Addr};
/// use std::str::FromStr;
/// use ipnet::IpBitAnd;
///
/// let ip0 = Ipv4Addr::from_str("0.0.0.0").unwrap();
/// let ip1 = Ipv4Addr::from_str("1.1.1.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("2.2.2.2").unwrap();
///
/// assert_eq!(ip0.bitand(ip1), Ipv4Addr::from_str("0.0.0.0").unwrap());
/// assert_eq!(ip1.bitand(ip1), Ipv4Addr::from_str("1.1.1.1").unwrap());
/// assert_eq!(ip1.bitand(ip2), Ipv4Addr::from_str("0.0.0.0").unwrap());
/// 
/// let ip60 = Ipv6Addr::from_str("::").unwrap();
/// let ip61 = Ipv6Addr::from_str("::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("::2").unwrap();
///
/// assert_eq!(ip60.bitand(ip61), Ipv6Addr::from_str("::").unwrap());
/// assert_eq!(ip61.bitand(ip61), Ipv6Addr::from_str("::1").unwrap());
/// assert_eq!(ip61.bitand(ip62), Ipv6Addr::from_str("::").unwrap());
/// ```
pub trait IpBitAnd<RHS = Self> {
    type Output;
    fn bitand(self, rhs: RHS) -> Self::Output;
}

/// Provides a `bitor()` method for `Ipv4Addr` and `Ipv6Addr`.
///
/// # Examples
///
/// ```
/// use std::net::{Ipv4Addr, Ipv6Addr};
/// use std::str::FromStr;
/// use ipnet::IpBitOr;
///
/// let ip0 = Ipv4Addr::from_str("0.0.0.0").unwrap();
/// let ip1 = Ipv4Addr::from_str("1.1.1.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("2.2.2.2").unwrap();
///
/// assert_eq!(ip0.bitor(ip1), Ipv4Addr::from_str("1.1.1.1").unwrap());
/// assert_eq!(ip1.bitor(ip1), Ipv4Addr::from_str("1.1.1.1").unwrap());
/// assert_eq!(ip1.bitor(ip2), Ipv4Addr::from_str("3.3.3.3").unwrap());
/// 
/// let ip60 = Ipv6Addr::from_str("::").unwrap();
/// let ip61 = Ipv6Addr::from_str("::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("::2").unwrap();
///
/// assert_eq!(ip60.bitor(ip61), Ipv6Addr::from_str("::1").unwrap());
/// assert_eq!(ip61.bitor(ip61), Ipv6Addr::from_str("::1").unwrap());
/// assert_eq!(ip61.bitor(ip62), Ipv6Addr::from_str("::3").unwrap());
/// ```
pub trait IpBitOr<RHS = Self> {
    type Output;
    fn bitor(self, rhs: RHS) -> Self::Output;
}

impl IpAdd<u32> for IpAddr {
    type Output = IpAddr;
    #[inline]
    fn saturating_add(self, rhs: u32) -> IpAddr {
        match self {
            IpAddr::V4(a) => IpAddr::V4(a.saturating_add(rhs)),
            IpAddr::V6(a) => IpAddr::V6(a.saturating_add(rhs)),
        }
    }    
}
/*
impl IpAdd<IpAddr> for IpAddr {
    type Output = IpAddr;
    #[inline]
    fn saturating_add(self, rhs: IpAddr) -> Result<IpAddr, Err> {
        match (self, rhs) {
            (IpAddr::V4(a), IpAddr::V4(b)) => a.saturating_add(b),
            (IpAddr::V6(a), IpAddr::V6(b)) => a.saturating_add(b),
            _ => 
        }
    }
}*/

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

macro_rules! ip_sub_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpSub<$f> for $t {
            type Output = $t;
            #[inline]
            fn saturating_sub(self, rhs: $f) -> $t {
                Self::from(u32::from(self).saturating_sub(u32::from(rhs)))
            }
        }
    )*
    }
}

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

macro_rules! ipv6_add_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpAdd<$f> for $t {
            type Output = $t;
            #[inline]
            fn saturating_add(self, rhs: $f) -> $t {
                let lhs: Emu128 = self.into();
                let rhs: Emu128 = rhs.into();
                (lhs.saturating_add(rhs.into())).into()
            }
        }
    )*
    }
}

macro_rules! ipv6_sub_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpSub<$f> for $t {
            type Output = $t;
            #[inline]
            fn saturating_sub(self, rhs: $f) -> $t {
                let lhs: Emu128 = self.into();
                let rhs: Emu128 = rhs.into();
                (lhs.saturating_sub(rhs.into())).into()
            }
        }
    )*
    }
}

macro_rules! ipv6_bitand_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitAnd<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitand(self, rhs: $f) -> $t {
                let lhs: Emu128 = self.into();
                let rhs: Emu128 = rhs.into();
                (lhs & rhs).into()
            }
        }
    )*
    }
}

macro_rules! ipv6_bitor_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitOr<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitor(self, rhs: $f) -> $t {
                let lhs: Emu128 = self.into();
                let rhs: Emu128 = rhs.into();
                (lhs | rhs).into()
            }
        }
    )*
    }
}

ip_add_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }
ip_sub_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }
ip_bitand_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }
ip_bitor_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }
ipv6_add_impl! { (Ipv6Addr, Emu128), (Ipv6Addr, u32), (Ipv6Addr, Ipv6Addr), }
ipv6_sub_impl! { (Ipv6Addr, Emu128), (Ipv6Addr, u32), (Ipv6Addr, Ipv6Addr), }
ipv6_bitand_impl! { (Ipv6Addr, Emu128), (Ipv6Addr, Ipv6Addr), }
ipv6_bitor_impl! { (Ipv6Addr, Emu128), (Ipv6Addr, Ipv6Addr), }
