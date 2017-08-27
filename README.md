This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. It only uses stable Rust features so it compiles using the stable toolchain. And its design aligns to the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations to `Ipv4Addr` and `Ipv6Addr`.

See [Crates.io] and the [documentation] for more information.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/
