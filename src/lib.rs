// Allow while hacking
#![allow(dead_code)]

pub use self::emu128::*;
pub use self::ipext::{ipv6_addr_from_emu128, ipv6_addr_into_emu128, IpAdd, IpSub, IpBitAnd, IpBitOr};
pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net, aggregate_ipv4_networks, aggregate_ipv6_networks};
pub use self::parser::AddrParseError;

mod emu128;
mod ipext;
mod ipnet;
// Not sure if there is a way to reuse and extend std::net::parser
// because it's private. So it's reimplemented in parser.rs to add
// parsing for network types.
mod parser;
mod saturating_shifts;