[![Build Status](https://travis-ci.org/krisprice/ipnet.svg?branch=master)](https://travis-ci.org/krisprice/ipnet)

Nearing 1.0 release, feedback and requests are very welcome. Just open an [issue on GitHub](https://github.com/krisprice/ipnet/issues) or email me.

This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. Its design aligns to and makes use of the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library. It will always use only the stable Rust features, so that it will always compile using the stable toolchain.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations and iterations to `Ipv4Addr` and `Ipv6Addr`.

Available on [Crates.io] and read the [documentation] for the full details.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/

## Future

* Explore representing the results of methods such as `hosts()` and `subnets()` as `Range`s. This requires both the `Add` and `Step` traits be implemented on the target types. For `IpAddr` this requires a change to the standard library. Also `Step` is still unstable, so exploring this will wait until it has stablized.
* Implementing the `{Add, Sub, BitAnd, BitOr}` traits for `Ipv4Addr` and `Ipv6Addr` would be useful as these are common operations on IP addresses. `Add` is also a precursor to implementing `Range` for these types. These require a change to the standard library. I've started a thread on this topic over on [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/) discussion board.

## License

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
