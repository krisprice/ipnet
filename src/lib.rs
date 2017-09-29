#![doc(html_root_url = "https://docs.rs/ipnet/1.0.0-rc1")]
//! Types for IPv4 and IPv6 network addresses.
//!
//! This module provides types and methods for working with IPv4 and
//! IPv6 network addresses, commonly called IP prefixes. Its design
//! aligns to and makes use of the existing [`IpAddr`], [`Ipv4Addr`],
//! and [`Ipv6Addr`] types provided in the Rust standard library.
//!
//! The module also provides traits that extend `Ipv4Addr` and
//! `Ipv6Addr` to support Add, Sub, BitAnd, and BitOr operations, and
//! iteration over an IP.
//!
//! # Organization
//!
//! * [`IpNet`] represents IP network addresses of either IPv4 or IPv6.
//! * [`Ipv4Net`] and [`Ipv6Net`] are respectively IPv4 and IPv6 network
//!   addresses.
//! * [`Subnets`] is an iterator that generates the valid IP network
//!   addresses bound by a given IP address range and minimum prefix
//!   length.
//! * [`IpAddrIter`] provides iteration over a range of IP addresses.
//! * The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//!   the `Ipv4Addr` and `Ipv6Addr` types with methods to perform these
//!   operations.
//! * [`Emu128`] is an emulated 128 bit unsigned integer implemented in
//!   this module using a struct of two `u64` types. This is necessary
//!   because Rust's `u128` type is not yet marked stable. This can be
//!   replaced when `u128` is stable.
//!
//! [`IpAddr`]: https://doc.rust-lang.org/std/net/enum.IpAddr.html
//! [`Ipv4Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv4Addr.html
//! [`Ipv6Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv6Addr.html
//! [`IpNet`]: enum.IpNet.html
//! [`Ipv4Net`]: struct.Ipv4Net.html
//! [`Ipv6Net`]: struct.Ipv6Net.html
//! [`Subnets`]: struct.Subnets.html
//! [`IpAddrIter`]: struct.IpAddrIter.html
//! [`IpAdd`]: trait.IpAdd.html
//! [`IpSub`]: trait.IpSub.html
//! [`IpBitAnd`]: trait.IpBitAnd.html
//! [`IpBitOr`]: trait.IpBitOr.html
//! [`Emu128`]: struct.Emu128.html

pub use self::emu128::Emu128;
pub use self::ipext::{IpAddrIter, IpAdd, IpSub, IpBitAnd, IpBitOr};
pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net, Contains, PrefixLenError, Subnets};
pub use self::parser::AddrParseError;

mod emu128;
mod ipext;
mod ipnet;
mod parser;
