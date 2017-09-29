[![Build Status](https://travis-ci.org/krisprice/ipnet.svg?branch=master)](https://travis-ci.org/krisprice/ipnet)

This module provides types and useful methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. The new `IpNet`, `Ipv4Net`, and `Ipv6Net` types build on the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types already provided in Rust's standard library and align to their design to stay consistent. The module also provides useful traits that extend `Ipv4Addr` and `Ipv6Addr` with methods for `Add`, `Sub`, `BitAnd`, and `BitOr` operations.

The module is guaranteed to compile using the stable toolchain. Testing is fairly extensive, and contained in test modules or the doctests. Please file an [issue on GitHub] if you have any problems, feedback, or requests.

Read the [documentation] for the full details. And find it on [Crates.io].

[documentation]: https://docs.rs/ipnet/
[Crates.io]: https://crates.io/crates/ipnet
[issue on GitHub]: https://github.com/krisprice/ipnet/issues

## Examples

```
// ...
```

## Future

* When `u128` is stablized it will replace `Emu128` and the major version will be incremented.
* Implementing `std::ops::{Add, Sub, BitAnd, BitOr}` for `Ipv4Addr` and `Ipv6Addr` would be useful as these are common operations on IP addresses. If done, the extension traits provided in this module would be removed and the major version incremented. Implementing these requires a change to the standard library. I've started a thread on this topic on the [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/) discussion board.
* The results of `hosts()` and potentially `subnets()` should be represented as a `Range` rather than the custom `IpAddrIter` and `Subnets` types provided in this module. This requires the target types to have `Add` and `Step` implemented for them. Implementing `Add` for `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` requires a change to the standard library (see above). And `Step` is still unstable so exploring this will also wait until it has stablized.

## License

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
