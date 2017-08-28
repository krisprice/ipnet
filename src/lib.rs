//! Types for IPv4 and IPv6 network addresses.
//!
//! This module provides types and methods for working with IPv4 and
//! IPv6 network addresses. It aims for alignment with the [`IpAddr`],
//! [`Ipv4Addr`], and [`Ipv6Addr`] types in Rust's standard library.
//!
//! The module also provides traits that extend `Ipv4Addr` and
//! `Ipv6Addr` to support Add, Sub, BitAnd, and BitOr operations.
//!
//! # Organization
//!
//! * [`IpNet`] represents IP network addresses of either IPv4 or IPv6.
//! * [`Ipv4Net`] and [`Ipv6Net`] are respectively IPv4 and IPv6 network
//!   addresses.
//! * [`IpAddrIter`] provides iteration over a range of IP addresses and
//!   [`IpNetIter`] does the same for IP network addresses. These are
//!   returned by methods on `IpNet`, `Ipv4Net`, and `Ipv6Net`.
//! * The [`IpAdd`], [`IpSub`], [`IpBitAnd`], [`IpBitOr`] traits extend
//!   the `Ipv4Addr` and `Ipv6Addr` types to include these operations.
//! * [`Emu128`] is an emulated 128 bit unsigned integer implemented in
//!   this module using a struct of two `u64` types. This is necessary
//!   because Rust's `u128` type is not yet marked stable. This can be
//!   replaced when `u128` is stable.
//!
//! # TODO:
//! * What's going on with AddrParseError(()) in parser.rs?
//! * Should we convert subnets() and aggregate() methods to iterators?
//! * Should new() truncate the input Ipv4Addr to the prefix_len and
//!   store that instead? Technically it doesn't matter, but users
//!   may expect one behavior over the other.
//! * Should new() precompute the netmask, hostmask, network, and
//!   broadcast addresses and store these to avoid recomputing
//!   everytime the methods are called?
//! * Can we implement the `std::ops::{Add, Sub, BitAnd, BitOr}` traits
//!   for `Ipv4Addr` and `Ipv6Addr` in the standard library? These are
//!   common operations on IP addresses.
//! * Explore the possibility of representing IP network addresses or
//!   the results of some methods such as `subnets()` as a `Range`.
//!   However, at this time many of the associated `Range` traits are
//!   still nightly-only experimental APIs.
//!
//! [`IpAddr`]: https://doc.rust-lang.org/std/net/enum.IpAddr.html
//! [`Ipv4Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv4Addr.html
//! [`Ipv6Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv6Addr.html
//! [`IpNet`]: enum.IpNet.html
//! [`Ipv4Net`]: struct.Ipv4Net.html
//! [`Ipv6Net`]: struct.Ipv6Net.html
//! [`IpAddrIter`]: struct.IpAddrIter.html
//! [`IpNetIter`]: struct.IpNetIter.html
//! [`IpAdd`]: trait.IpAdd.html
//! [`IpSub`]: trait.IpAdd.html
//! [`IpBitAnd`]: trait.IpAdd.html
//! [`IpBitOr`]: trait.IpAdd.html
//! [`Emu128`]: struct.Emu128.html

pub use self::emu128::Emu128;
pub use self::ipext::{IpAddrIter, IpAdd, IpSub, IpBitAnd, IpBitOr};
pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net, IpNetIter};
pub use self::parser::AddrParseError;

mod emu128;
mod ipext;
mod ipnet;
mod parser;
mod saturating_shifts;
