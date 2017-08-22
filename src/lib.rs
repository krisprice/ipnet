//! Types for IPv4 and IPv6 network addresses.
//!
//! This module provides types and methods for working with IPv4 and
//! IPv6 network addresses. It aims for alignment with the [`IpAddr`],
//! [`Ipv4Addr`], and [`Ipv6Addr`] types in Rust's standard library.
//!
//! The module includes extension traits to add Add, Sub, BitAnd, and
//! BitOr operations to `Ipv4Addr` and `Ipv6Addr`.
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
//! * Implement tests and complete documentation of `IpNet`, etc.
//! * Convert subnets() and aggregate() methods to iterators?
//! * Can we implement the `std::ops::{Add, Sub, BitAnd, BitOr}` traits
//!   for `Ipv4Addr` and `Ipv6Addr` in the standard library? These are
//!   common operations on IP addresses.
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
//! [`ipv6_addr_from_emu128`]: 
//! [`ipv6_addr_into_emu128`]: 
//! [`emu128`]: struct.emu128.html

pub use self::emu128::{emu128 as Emu128}; // work around conflict with mod name
pub use self::ipext::{IpAdd, IpSub, IpBitAnd, IpBitOr};
pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net};
pub use self::parser::AddrParseError;

mod emu128;
mod ipext;
mod ipnet;
mod parser;
mod saturating_shifts;
