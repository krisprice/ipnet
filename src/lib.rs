// Allow while hacking
#![allow(dead_code)]

pub use self::ipnet::{IpNet, Ipv4Net, Ipv6Net, ipv6_addr_from_double_u64, ipv6_addr_into_double_u64};
pub use self::parser::AddrParseError;

mod ipnet;
// Not sure if there is a way to reuse and extend std::net::parser
// because it's private. So it's reimplemented in parser.rs to add
// parsing for network types.
mod parser;
mod saturating_shifts;
