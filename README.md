Nearing 1.0 release, reviews very welcome.

This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. It only uses stable Rust features so it compiles using the stable toolchain. And its design aligns to the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations to `Ipv4Addr` and `Ipv6Addr`.

Available on [Crates.io] and read the [documentation] for the full details.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/

## TODO / Open Questions:

* Should new() truncate the input Ipv4Addr to the prefix_len and store that instead? Technically it doesn't matter, but users may expect one behavior over the other. At the moment there is a trunc() method that does this.
* Can we implement the std::ops::{Add, Sub, BitAnd, BitOr} traits for Ipv4Addr and Ipv6Addr in the standard library? These are common operations on IP addresses. I've started a thread on this over here: https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/

## Future

* Explore representing the results of methods such as hosts() and subnets() as a Range. This requires both the Add and Step traits be implemented on the target type. For the three IpAddr types implementing Add must be done through an enhancement to the standard library. For all types, using Step means we must use nightly because it is not yet stable. This crate only uses stable Rust features.

## Legal

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
