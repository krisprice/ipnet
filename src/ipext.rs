//! Extensions to the standard IP address types for common operations.
//!
//! The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//! the `Ipv4Addr` and `Ipv6Addr` types to provide their respective
//! operations.

use std::cmp::Ordering::{Less, Equal};
use std::mem;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use emu128::Emu128;

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
    start: T,
    end: T,
}

impl<T> IpAddrIter<T> {
    pub fn new(start: T, end: T) -> Self {
        IpAddrIter {
            start: start,
            end: end,
        }
    }
}

// A barebones copy of the current unstable Step trait.
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

impl<T> Iterator for IpAddrIter<T>
    where T: Copy + PartialOrd + IpStep {
    type Item = T;

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
/// # Panics
///
/// When attempting to add an `IpAddr::V4` from an `IpAddr::V6` and vice
/// versa.
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
/// # Panics
///
/// When attempting to subtract an `IpAddr::V4` from an `IpAddr::V6` and
/// vice versa.
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

/*impl IpAdd<IpAddr> for IpAddr {
    type Output = IpAddr;

    #[inline]
    fn saturating_add(self, rhs: IpAddr) -> IpAddr {
        match (self, rhs) {
            (IpAddr::V4(a), IpAddr::V4(b)) => IpAddr::V4(a.saturating_add(b)),
            (IpAddr::V6(a), IpAddr::V6(b)) => IpAddr::V6(a.saturating_add(b)),
            _ => panic!("can't add Ipv4Addr and Ipv6Addr"),
        }
    }
}*/

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

/*impl IpSub<IpAddr> for IpAddr {
    type Output = IpAddr;

    #[inline]
    fn saturating_sub(self, rhs: IpAddr) -> IpAddr {
        match (self, rhs) {
            (IpAddr::V4(a), IpAddr::V4(b)) => IpAddr::V4(a.saturating_sub(b)),
            (IpAddr::V6(a), IpAddr::V6(b)) => IpAddr::V6(a.saturating_sub(b)),
            _ => panic!("can't subtract Ipv4Addr and Ipv6Addr"),
        }
    }
}*/
/*
impl IpAdd<u32> for Ipv4Addr {
    type Output = Ipv4Addr;

    fn saturating_add(self, rhs: u32) -> Ipv4Addr {
        let lhs: u32 = self.into();
        let rhs: u32 = rhs.into();
        lhs.saturating_add(rhs).into()
    }
}

impl IpSub<Ipv4Addr> for Ipv4Addr {
    type Output = u32;

    fn saturating_sub(self, rhs: Ipv4Addr) -> u32 {
        let lhs: u32 = self.into();
        let rhs: u32 = rhs.into();
        lhs.saturating_sub(rhs)
    }
}

impl IpSub<u32> for Ipv4Addr {
    type Output = Ipv4Addr;

    fn saturating_sub(self, rhs: u32) -> Ipv4Addr {
        let lhs: u32 = self.into();
        let rhs: u32 = rhs.into();
        lhs.saturating_sub(rhs).into()
    }
}*/

/*macro_rules! ip_addsub_impl {
    ($(($lhs:ty, $rhs:ty, $t:ty),)*) => {
    $(
        impl IpAdd<$rhs> for $lhs {
            type Output = $lhs;

            #[inline]
            fn saturating_add(self, rhs: $rhs) -> $lhs {
                let lhs: $t = self.into();
                let rhs: $t = rhs.into();
                (lhs.saturating_add(rhs.into())).into()
            }
        }

        impl IpSub<$rhs> for $lhs {
            type Output = $lhs;

            #[inline]
            fn saturating_sub(self, rhs: $rhs) -> $lhs {
                let lhs: $t = self.into();
                let rhs: $t = rhs.into();
                (lhs.saturating_sub(rhs.into())).into()
            }
        }
    )*
    }
}*/

macro_rules! ip_addsub_impl {
    ($(($lhs:ty, $rhs:ty, $output:ty, $inner:ty),)*) => {
    $(
        impl IpAdd<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn saturating_add(self, rhs: $rhs) -> $output {
                let lhs: $inner = self.into();
                let rhs: $inner = rhs.into();
                (lhs.saturating_add(rhs.into())).into()
            }
        }

        impl IpSub<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn saturating_sub(self, rhs: $rhs) -> $output {
                let lhs: $inner = self.into();
                let rhs: $inner = rhs.into();
                (lhs.saturating_sub(rhs.into())).into()
            }
        }
    )*
    }
}

// lhs, rhs, output, inner type
ip_addsub_impl! {
    (Ipv4Addr, Ipv4Addr, u32, u32),
    (Ipv4Addr, u32, Ipv4Addr, u32),
    (Ipv6Addr, Ipv6Addr, Emu128, Emu128),
    (Ipv6Addr, Emu128, Ipv6Addr, Emu128),
    (Ipv6Addr, u32, Ipv6Addr, Emu128),
}

/*ip_addsub_impl! {
    (Ipv4Addr, Ipv4Addr, u32),
    (Ipv4Addr, u32, u32),
    (Ipv6Addr, Ipv6Addr, Emu128),
    (Ipv6Addr, Emu128, Emu128),
    (Ipv6Addr, u32, Emu128),
}*/

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
    fn test_ipaddriter() {
        let i = IpAddrIter::new(IpAddr::from_str("10.0.0.0").unwrap(), IpAddr::from_str("10.0.0.3").unwrap());
        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("10.0.0.0").unwrap(),
            IpAddr::from_str("10.0.0.1").unwrap(),
            IpAddr::from_str("10.0.0.2").unwrap(),
            IpAddr::from_str("10.0.0.3").unwrap(),
        ]);

        let i = IpAddrIter::new(IpAddr::from_str("255.255.255.254").unwrap(), IpAddr::from_str("255.255.255.255").unwrap());
        assert_eq!(i.collect::<Vec<IpAddr>>(), vec![
            IpAddr::from_str("255.255.255.254").unwrap(),
            IpAddr::from_str("255.255.255.255").unwrap(),
        ]);

        let i = IpAddrIter::new(Ipv4Addr::from_str("10.0.0.0").unwrap(), Ipv4Addr::from_str("10.0.0.3").unwrap());
        assert_eq!(i.collect::<Vec<Ipv4Addr>>(), vec![
            Ipv4Addr::from_str("10.0.0.0").unwrap(),
            Ipv4Addr::from_str("10.0.0.1").unwrap(),
            Ipv4Addr::from_str("10.0.0.2").unwrap(),
            Ipv4Addr::from_str("10.0.0.3").unwrap(),
        ]);

        let i = IpAddrIter::new(Ipv4Addr::from_str("255.255.255.254").unwrap(), Ipv4Addr::from_str("255.255.255.255").unwrap());
        assert_eq!(i.collect::<Vec<Ipv4Addr>>(), vec![
            Ipv4Addr::from_str("255.255.255.254").unwrap(),
            Ipv4Addr::from_str("255.255.255.255").unwrap(),
        ]);

        let i = IpAddrIter::new(Ipv6Addr::from_str("fd00::").unwrap(), Ipv6Addr::from_str("fd00::3").unwrap());
        assert_eq!(i.collect::<Vec<Ipv6Addr>>(), vec![
            Ipv6Addr::from_str("fd00::").unwrap(),
            Ipv6Addr::from_str("fd00::1").unwrap(),
            Ipv6Addr::from_str("fd00::2").unwrap(),
            Ipv6Addr::from_str("fd00::3").unwrap(),
        ]);
    }

    #[test]
    #[should_panic]
    fn test_ipaddr_add() {
        let ip4 = IpAddr::from_str("10.1.1.1").unwrap();
        let ip6 = IpAddr::from_str("::1").unwrap();
        ip4.saturating_add(ip6);
    }
    
    #[test]
    #[should_panic]
    fn test_ipaddr_sub() {
        let ip4 = IpAddr::from_str("10.1.1.1").unwrap();
        let ip6 = IpAddr::from_str("::1").unwrap();
        ip4.saturating_sub(ip6);
    }
}