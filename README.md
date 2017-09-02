Nearing 1.0 release, reviews very welcome.

This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. It only uses stable Rust features so it compiles using the stable toolchain. And its design aligns to the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations to `Ipv4Addr` and `Ipv6Addr`.

See [Crates.io] and the [documentation] for more information.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
