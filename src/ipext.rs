//! Extensions to the standard IP address types for common operations.
//!
//! The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//! the `Ipv4Addr` and `Ipv6Addr` types with methods to perform these
//! operations.

use std::cmp::Ordering::{Less, Equal};
use std::mem;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use emu128::Emu128;

// A barebones copy of the current unstable Step trait used by the
// IpAddrRange, Ipv4AddrRange, and Ipv6AddrRange types below, and the
// Subnets types in ipnet.
pub trait IpStep {
    fn replace_zero(&mut self) -> Self;
    fn add_one(&self) -> Self;
}

impl IpStep for IpAddr {
    fn replace_zero(&mut self) -> Self {
        match *self {
            IpAddr::V4(ref mut a) => IpAddr::V4(a.replace_zero()),
            IpAddr::V6(ref mut a) => IpAddr::V6(a.replace_zero()),
        }
    }
    fn add_one(&self) -> Self {
        self.saturating_add(1)   
    }
}

impl IpStep for Ipv4Addr {
    fn replace_zero(&mut self) -> Self {
        mem::replace(self, Ipv4Addr::new(0, 0, 0, 0))
    }
    fn add_one(&self) -> Self {
        self.saturating_add(1)
    }
}

impl IpStep for Ipv6Addr {
    fn replace_zero(&mut self) -> Self {
        mem::replace(self, Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0))
    }
    fn add_one(&self) -> Self {
        self.saturating_add(1)
    }
}

/// An `Iterator` over a range of IP addresses, either IPv4 or IPv6.
///
/// # Examples
///
/// ```
/// # use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
/// # use std::str::FromStr;
/// # use ipnet::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
/// let hosts = IpAddrRange::from(Ipv4AddrRange::new(
///     Ipv4Addr::from_str("10.0.0.0").unwrap(),
///     Ipv4Addr::from_str("10.0.0.3").unwrap(),
/// ));
///
/// assert_eq!(hosts.collect::<Vec<IpAddr>>(), vec![
///     IpAddr::from_str("10.0.0.0").unwrap(),
///     IpAddr::from_str("10.0.0.1").unwrap(),
///     IpAddr::from_str("10.0.0.2").unwrap(),
///     IpAddr::from_str("10.0.0.3").unwrap(),
/// ]);
///
/// let hosts = IpAddrRange::from(Ipv6AddrRange::new(
///     Ipv6Addr::from_str("fd00::").unwrap(),
///     Ipv6Addr::from_str("fd00::3").unwrap(),
/// ));
///
/// assert_eq!(hosts.collect::<Vec<IpAddr>>(), vec![
///     IpAddr::from_str("fd00::").unwrap(),
///     IpAddr::from_str("fd00::1").unwrap(),
///     IpAddr::from_str("fd00::2").unwrap(),
///     IpAddr::from_str("fd00::3").unwrap(),
/// ]);
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum IpAddrRange {
    V4(Ipv4AddrRange),
    V6(Ipv6AddrRange),
}

/// An `Iterator` over a range of IPv4 addresses.
///
/// # Examples
///
/// ```
/// # use std::net::Ipv4Addr;
/// # use std::str::FromStr;
/// # use ipnet::Ipv4AddrRange;
/// let hosts = Ipv4AddrRange::new(
///     Ipv4Addr::from_str("10.0.0.0").unwrap(),
///     Ipv4Addr::from_str("10.0.0.3").unwrap(),
/// );
///
/// assert_eq!(hosts.collect::<Vec<Ipv4Addr>>(), vec![
///     Ipv4Addr::from_str("10.0.0.0").unwrap(),
///     Ipv4Addr::from_str("10.0.0.1").unwrap(),
///     Ipv4Addr::from_str("10.0.0.2").unwrap(),
///     Ipv4Addr::from_str("10.0.0.3").unwrap(),
/// ]);
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Ipv4AddrRange {
    start: Ipv4Addr,
    end: Ipv4Addr,
}

/// An `Iterator` over a range of IPv4 or IPv6 addresses.
///
/// # Examples
///
/// ```
/// # use std::net::Ipv6Addr;
/// # use std::str::FromStr;
/// # use ipnet::Ipv6AddrRange;
/// let hosts = Ipv6AddrRange::new(
///     Ipv6Addr::from_str("fd00::").unwrap(),
///     Ipv6Addr::from_str("fd00::3").unwrap(),
/// );
///
/// assert_eq!(hosts.collect::<Vec<Ipv6Addr>>(), vec![
///     Ipv6Addr::from_str("fd00::").unwrap(),
///     Ipv6Addr::from_str("fd00::1").unwrap(),
///     Ipv6Addr::from_str("fd00::2").unwrap(),
///     Ipv6Addr::from_str("fd00::3").unwrap(),
/// ]);
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Ipv6AddrRange {
    start: Ipv6Addr,
    end: Ipv6Addr,
}

impl Ipv4AddrRange {
    pub fn new(start: Ipv4Addr, end: Ipv4Addr) -> Self {
        Ipv4AddrRange {
            start: start,
            end: end,
        }
    }
}

impl Ipv6AddrRange {
    pub fn new(start: Ipv6Addr, end: Ipv6Addr) -> Self {
        Ipv6AddrRange {
            start: start,
            end: end,
        }
    }
}

impl From<Ipv4AddrRange> for IpAddrRange {
    fn from(i: Ipv4AddrRange) -> IpAddrRange {
        IpAddrRange::V4(i)
    }
}

impl From<Ipv6AddrRange> for IpAddrRange {
    fn from(i: Ipv6AddrRange) -> IpAddrRange {
        IpAddrRange::V6(i)
    }
}

impl Iterator for IpAddrRange {
    type Item = IpAddr;

    fn next(&mut self) -> Option<Self::Item> {
        match *self {
            IpAddrRange::V4(ref mut a) => a.next().map(IpAddr::V4),
            IpAddrRange::V6(ref mut a) => a.next().map(IpAddr::V6),
        }
    }
}

impl Iterator for Ipv4AddrRange {
    type Item = Ipv4Addr;

    fn next(&mut self) -> Option<Self::Item> {
        match self.start.partial_cmp(&self.end) {
            Some(Less) => {
                let next = self.start.add_one();
                Some(mem::replace(&mut self.start, next))
            },
            Some(Equal) => {
                self.end.replace_zero();
                Some(self.start)
            },
            _ => None,
        }
    }
}

impl Iterator for Ipv6AddrRange {
    type Item = Ipv6Addr;

    fn next(&mut self) -> Option<Self::Item> {
        match self.start.partial_cmp(&self.end) {
            Some(Less) => {
                let next = self.start.add_one();
                Some(mem::replace(&mut self.start, next))
            },
            Some(Equal) => {
                self.end.replace_zero();
                Some(self.start)
            },
            _ => None,
        }
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
/// let ip1 = Ipv4Addr::from_str("0.0.0.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("255.255.255.254").unwrap();
/// let ip3 = Ipv4Addr::from_str("255.255.255.255").unwrap();
///
/// assert_eq!(ip0.saturating_add(1u32), ip1);
/// assert_eq!(ip2.saturating_add(1u32), ip3);
/// assert_eq!(ip2.saturating_add(1u32), ip3);
///
/// let ip60 = Ipv6Addr::from_str("fd00::").unwrap();
/// let ip61 = Ipv6Addr::from_str("fd00::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap();
/// let ip63 = Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap();
///
/// assert_eq!(ip60.saturating_add(1u32), ip61);
/// assert_eq!(ip62.saturating_add(1u32), ip63);
/// assert_eq!(ip62.saturating_add(1u32), ip63);
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
/// use ipnet::{IpSub, Emu128};
///
/// let ip0 = Ipv4Addr::from_str("0.0.0.0").unwrap();
/// let ip1 = Ipv4Addr::from_str("0.0.0.1").unwrap();
/// let ip2 = Ipv4Addr::from_str("0.0.0.2").unwrap();
///
/// assert_eq!(ip0.saturating_sub(ip1), 0);
/// assert_eq!(ip2.saturating_sub(ip1), 1);
/// assert_eq!(ip0.saturating_sub(1u32), ip0);
/// assert_eq!(ip2.saturating_sub(1u32), ip1);
/// 
/// let ip60 = Ipv6Addr::from_str("::").unwrap();
/// let ip61 = Ipv6Addr::from_str("::1").unwrap();
/// let ip62 = Ipv6Addr::from_str("::2").unwrap();
///
/// assert_eq!(ip60.saturating_sub(ip61), Emu128::from(0));
/// assert_eq!(ip62.saturating_sub(ip61), Emu128::from(1));
/// assert_eq!(ip60.saturating_sub(1u32), ip60);
/// assert_eq!(ip62.saturating_sub(1u32), ip61);
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

impl IpSub<u32> for IpAddr {
    type Output = IpAddr;

    #[inline]
    fn saturating_sub(self, rhs: u32) -> IpAddr {
        match self {
            IpAddr::V4(a) => IpAddr::V4(a.saturating_sub(rhs)),
            IpAddr::V6(a) => IpAddr::V6(a.saturating_sub(rhs)),
        }
    }
}

macro_rules! ip_add_impl {
    ($lhs:ty, $rhs:ty, $output:ty, $inner:ty) => (
        impl IpAdd<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn saturating_add(self, rhs: $rhs) -> $output {
                let lhs: $inner = self.into();
                let rhs: $inner = rhs.into();
                (lhs.saturating_add(rhs.into())).into()
            }
        }
    )
}

macro_rules! ip_sub_impl {
    ($lhs:ty, $rhs:ty, $output:ty, $inner:ty) => (
        impl IpSub<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn saturating_sub(self, rhs: $rhs) -> $output {
                let lhs: $inner = self.into();
                let rhs: $inner = rhs.into();
                (lhs.saturating_sub(rhs.into())).into()
            }
        }
    )
}

ip_add_impl!(Ipv4Addr, u32, Ipv4Addr, u32);
ip_add_impl!(Ipv6Addr, Emu128, Ipv6Addr, Emu128);
ip_add_impl!(Ipv6Addr, u32, Ipv6Addr, Emu128);

ip_sub_impl!(Ipv4Addr, Ipv4Addr, u32, u32);
ip_sub_impl!(Ipv4Addr, u32, Ipv4Addr, u32);
ip_sub_impl!(Ipv6Addr, Ipv6Addr, Emu128, Emu128);
ip_sub_impl!(Ipv6Addr, Emu128, Ipv6Addr, Emu128);
ip_sub_impl!(Ipv6Addr, u32, Ipv6Addr, Emu128);

macro_rules! ip_bitops_impl {
    ($(($lhs:ty, $rhs:ty, $t:ty),)*) => {
    $(
        impl IpBitAnd<$rhs> for $lhs {
            type Output = $lhs;

            #[inline]
            fn bitand(self, rhs: $rhs) -> $lhs {
                let lhs: $t = self.into();
                let rhs: $t = rhs.into();
                (lhs & rhs).into()
            }
        }

        impl IpBitOr<$rhs> for $lhs {
            type Output = $lhs;

            #[inline]
            fn bitor(self, rhs: $rhs) -> $lhs {
                let lhs: $t = self.into();
                let rhs: $t = rhs.into();
                (lhs | rhs).into()
            }
        }
    )*
    }
}

ip_bitops_impl! {
    (Ipv4Addr, Ipv4Addr, u32),
    (Ipv4Addr, u32, u32),
    (Ipv6Addr, Ipv6Addr, Emu128),
    (Ipv6Addr, Emu128, Emu128),
}

#[cfg(test)]
mod tests {
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    use std::str::FromStr;
    use super::*;

    #[test]
    fn test_ipaddrrange() {
        let i = Ipv4AddrRange::new(
            Ipv4Addr::from_str("10.0.0.0").unwrap(),
            Ipv4Addr::from_str("10.0.0.3").unwrap()
        );

        assert_eq!(i.collect::<Vec<Ipv4Addr>>(), vec![
            Ipv4Addr::from_str("10.0.0.0").unwrap(),
            Ipv4Addr::from_str("10.0.0.1").unwrap(),
            Ipv4Addr::from_str("10.0.0.2").unwrap(),
            Ipv4Addr::from_str("10.0.0.3").unwrap(),
        ]);

        let i = Ipv4AddrRange::new(
            Ipv4Addr::from_str("255.255.255.254").unwrap(),
            Ipv4Addr::from_str("255.255.255.255").unwrap()
        );

        assert_eq!(i.collect::<Vec<Ipv4Addr>>(), vec![
            Ipv4Addr::from_str("255.255.255.254").unwrap(),
            Ipv4Addr::from_str("255.255.255.255").unwrap(),
        ]);

        let i = Ipv6AddrRange::new(
            Ipv6Addr::from_str("fd00::").unwrap(),
            Ipv6Addr::from_str("fd00::3").unwrap(),
        );

        assert_eq!(i.collect::<Vec<Ipv6Addr>>(), vec![
            Ipv6Addr::from_str("fd00::").unwrap(),
            Ipv6Addr::from_str("fd00::1").unwrap(),
            Ipv6Addr::from_str("fd00::2").unwrap(),
            Ipv6Addr::from_str("fd00::3").unwrap(),
        ]);

        let i = Ipv6AddrRange::new(
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap(),
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap(),
        );

        assert_eq!(i.collect::<Vec<Ipv6Addr>>(), vec![
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap(),
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap(),
        ]);
        
        let i = IpAddrRange::from(Ipv4AddrRange::new(
            Ipv4Addr::from_str("10.0.0.0").unwrap(),
            Ipv4Addr::from_str("10.0.0.3").unwrap(),
        ));

        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("10.0.0.0").unwrap(),
            IpAddr::from_str("10.0.0.1").unwrap(),
            IpAddr::from_str("10.0.0.2").unwrap(),
            IpAddr::from_str("10.0.0.3").unwrap(),
        ]);
        
        let i = IpAddrRange::from(Ipv4AddrRange::new(
            Ipv4Addr::from_str("255.255.255.254").unwrap(),
            Ipv4Addr::from_str("255.255.255.255").unwrap()
        ));

        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("255.255.255.254").unwrap(),
            IpAddr::from_str("255.255.255.255").unwrap(),
        ]);

        let i = IpAddrRange::from(Ipv6AddrRange::new(
            Ipv6Addr::from_str("fd00::").unwrap(),
            Ipv6Addr::from_str("fd00::3").unwrap(),
        ));

        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("fd00::").unwrap(),
            IpAddr::from_str("fd00::1").unwrap(),
            IpAddr::from_str("fd00::2").unwrap(),
            IpAddr::from_str("fd00::3").unwrap(),
        ]);

        let i = IpAddrRange::from(Ipv6AddrRange::new(
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap(),
            Ipv6Addr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap(),
        ));

        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffe").unwrap(),
            IpAddr::from_str("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap(),
        ]);
    }
}