#![doc(html_root_url = "https://docs.rs/ipnet/2.0.0-rc1")]
//! Types for IPv4 and IPv6 network addresses.
//!
//! This module provides types and useful methods for working with IPv4
//! and IPv6 network addresses, commonly called IP prefixes. The new
//! [`IpNet`], [`Ipv4Net`], and [`Ipv6Net`] types build on the existing
//! [`IpAddr`], [`Ipv4Addr`], and [`Ipv6Addr`] types already provided in
//! Rust's standard library and align to their design to stay
//! consistent.
//! 
//! The module also provides types for iterating over IP address ranges,
//! and useful traits that extend [`Ipv4Addr`] and [`Ipv6Addr`] with
//! methods for addition, subtraction, bitwise-and, and bitwise-or
//! operations that are missing in Rust's standard library.
//!
//! The module only uses stable features so it is guaranteed to compile
//! using the stable toolchain.
//!
//! # Organization
//!
//! * [`IpNet`] represents an IP network address, either IPv4 or IPv6.
//! * [`Ipv4Net`] and [`Ipv6Net`] are respectively IPv4 and IPv6 network
//!   addresses.
//! * [`IpSubnets`], [`Ipv4Subnets`], and [`Ipv6Subnets`] are iterators
//!   that generate the smallest set of IP network addresses bound by an
//!   IP address range and minimum prefix length. These are returned by
//!   the [`subnets()`] methods and used in the [`aggregate()`] methods.
//! * [`IpAddrRange`], [`Ipv4AddrRange`], and [`Ipv6AddrRange`] provide
//!   iteration over ranges of IP addresses. These are returned by the
//!   [`hosts()`] methods.
//! * The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//!   the [`Ipv4Addr`] and [`Ipv6Addr`] types with methods to perform
//!   these operations.
//! * [`Emu128`] is an emulated 128 bit unsigned integer implemented in
//!   this module using a struct of two `u64` types. This is useful for
//!   operations on IPv6 address, which are 128 bit unsigned integers.
//!
//! [`IpNet`]: enum.IpNet.html
//! [`Ipv4Net`]: struct.Ipv4Net.html
//! [`Ipv6Net`]: struct.Ipv6Net.html
//! [`IpAddr`]: https://doc.rust-lang.org/std/net/enum.IpAddr.html
//! [`Ipv4Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv4Addr.html
//! [`Ipv6Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv6Addr.html
//! [`IpSubnets`]: enum.IpSubnets.html
//! [`Ipv4Subnets`]: struct.Ipv4Subnets.html
//! [`Ipv6Subnets`]: struct.Ipv6Subnets.html
//! [`subnets()`]: enum.IpNet.html#method.subnets
//! [`aggregate()`]: enum.IpNet.html#method.aggregate
//! [`IpAddrRange`]: enum.IpAddrRange.html
//! [`Ipv4AddrRange`]: struct.Ipv4AddrRange.html
//! [`Ipv6AddrRange`]: struct.Ipv6AddrRange.html
//! [`hosts()`]: enum.IpNet.html#method.hosts
//! [`IpAdd`]: trait.IpAdd.html
//! [`IpSub`]: trait.IpSub.html
//! [`IpBitAnd`]: trait.IpBitAnd.html
//! [`IpBitOr`]: trait.IpBitOr.html
//! [`Emu128`]: struct.Emu128.html
//!
//! # Serde support
//!
//! This library comes with support for [serde](https://serde.rs) but it's
//! not enabled by default. Use the `serde` [feature] to enable.
//! 
//! IpNet, Ipv4Net, and Ipv6Net will serialize to their `Display` strings
//! for human readable formats (e.g. JSON).
//! 
//! Ipv4Net and Ipv6Net will serialize to a string of 5 and 17 bytes
//! respectively for compact (binary) formats (e.g. Bincode). These are
//! the octets of the address followed by the prefix length. In the
//! case of IpNet it will serialize to an Enum with the variant index
//! prepending the string of bytes.
//! 
//! Serde support for compact formats should be considered semi-unstable
//! at this time.
//!
//! [feature]: https://doc.rust-lang.org/cargo/reference/manifest.html#the-features-section

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

pub use self::ipext::{IpAdd, IpSub, IpBitAnd, IpBitOr, IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net, Contains, PrefixLenError, IpSubnets, Ipv4Subnets, Ipv6Subnets};
pub use self::parser::AddrParseError;

mod ipext;
mod ipnet;
mod parser;
#[cfg(feature = "serde")]
mod ipnet_serde;
