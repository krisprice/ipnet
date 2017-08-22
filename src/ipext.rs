//! Types for IPv4 and IPv6 network addresses.
//!
//! This module provides types and methods for working with IPv4 and
//! IPv6 network addresses. It aims for alignment with the [`IpAddr`],
//! [`Ipv4Addr`], and [`Ipv6Addr`] types in Rust's standard library.
//! 
//! The module includes some extensions to these IP address types for
//! Add, Sub, BitAnd, and BitOr operations.
//!
//! # Organization
//!
//! * [`IpNet`] represents IP network addresses of either IPv4 or IPv6.
//! * [`Ipv4Net`] and [`Ipv6Net`] are respectively IPv4 and IPv6 network
//!   addresses.
//! * The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//!   the `Ipv4Addr` and `Ipv6Addr` types to include these operations. 
//! * [`ipv6_addr_from_emu128`] and [`ipv6_addr_into_emu128`] functions
//!   convert the between the Ipv6Addr type and the [`emu128`] type.
//! * [`emu128`] is an emulated 128 bit unsigned integer implemented in
//!   this module using a struct of two `u64` types. This is necessary
//!   because Rust's `u128` type is not yet marked stable. This can be
//!   replaced when `u128` is stable.
//!
//! # TODO:
//!
//! * Explore the possibility of representing IP network addresses as a
//!   `Range` using Rust's `RangeArgument` trait. `RangeArgument` and
//!   many of the associated `Range` methods are still nightly-only
//!   experimental APIs.
//!
//! [`IpAddr`]: https://doc.rust-lang.org/std/net/enum.IpAddr.html
//! [`Ipv4Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv4Addr.html
//! [`Ipv6Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv6Addr.html
//! [`IpNet`]: enum.IpNet.html
//! [`Ipv4Net`]: struct.Ipv4Net.htm
//! [`Ipv6Net`]: struct.Ipv6Net.html


use std::net::{Ipv4Addr, Ipv6Addr};
use emu128::emu128;

/// Convert an emulated u128 to an Ipv6Addr.
///
/// TODO: It would be nice to implement From on Ipv6Addr for this.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::ipv6_addr_from_double_u64;
/// assert_eq!(ipv6_addr_from_double_u64([0u64, 1u64]), Ipv6Addr::from_str("::1").unwrap());
/// ```
pub fn ipv6_addr_from_emu128(ip: emu128) -> Ipv6Addr {
    Ipv6Addr::new(
        (ip.hi >> 48) as u16, (ip.hi >> 32) as u16, (ip.hi >> 16) as u16, ip.hi as u16,
        (ip.lo >> 48) as u16, (ip.lo >> 32) as u16, (ip.lo >> 16) as u16, ip.lo as u16
    )
}

/// Convert an Ipv6Addr to an emulated u128.
///
/// TODO: It would be nice to implement From on Ipv6Addr for this.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::ipv6_addr_into_double_u64;
/// assert_eq!(ipv6_addr_into_double_u64(Ipv6Addr::from_str("::1").unwrap()), [0u64, 1u64]);
/// ```
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
}

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
        ipv6_addr_from_emu128(ipv6_addr_into_emu128(self) & rhs)
    }
}

impl IpBitOr<emu128> for Ipv6Addr {
    type Output = Ipv6Addr;
    #[inline]
    fn bitor(self, rhs: emu128) -> Ipv6Addr {
        ipv6_addr_from_emu128(ipv6_addr_into_emu128(self) | rhs)
    }
}
