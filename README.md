Nearing 1.0 release, feedback and code reviews are very welcome. Open an issue or comment here on the [Reddit post](https://www.reddit.com/r/rust/comments/6xk3jh/first_crate_ipnet_types_and_methods_for_network/).

This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. It only uses stable Rust features so that it compiles using the stable toolchain. And its design aligns to the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations to `Ipv4Addr` and `Ipv6Addr`.

Available on [Crates.io] and read the [documentation] for the full details.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/

## Open Questions:

* Should `IpNet::new()` truncate the input `IpAddr` to `prefix_len` and store that instead of the original unmodified address? Users may expect one behavior over the other. Truncating it at creation time means that the provided address cannot be returned later if the user has a need for it. Also, sort behavior will not be influence by it, e.g. `10.1.1.1/24` and `10.1.1.2/24` would be the same. There is a `trunc()` method that does this after creation, but chaining `IpNet::new(...).trunc()` or `IpNet::from_str().unwrap().trunc()` is tedious. Perhaps this should be solved with a second `new_with_trunc()` constructor. Or perhaps a series of [builder methods](https://rust-lang-nursery.github.io/api-guidelines/type-safety.html#non-consuming-builders-preferred)?
* Should `prefix_len` be it's own type? This seems like newtype overload, but the API guidelines would tend to indicate it [should be](https://rust-lang-nursery.github.io/api-guidelines/dependability.html).
* The guidelines suggest `subnets()` and `hosts()` should return types called `Subnets` and `Hosts` respectively rather than the generic `IpNetIter<T>` they currently return. See [here](https://rust-lang-nursery.github.io/api-guidelines/naming.html#iterator-type-names-match-the-methods-that-produce-them-c-iter-ty).

## Future

* Some of the proposals to support default arguments would be useful for solving the truncation question, that way the default could be to truncate, and the user can override this if they don't want that behaviour.
* Explore representing the results of methods such as `hosts()` and `subnets()` as `Range`s. This requires both the `Add` and `Step` traits be implemented on the target types. For `IpAddr` this requires a change to the standard library. `Step` is still unstable, so exploring this must wait until it has stablized.
* Implementing the `{Add, Sub, BitAnd, BitOr}` traits for Ipv4Addr and Ipv6Addr would be useful as these are common operations on IP addresses. This requires a change to the standard library. I've started a thread on this topic over on [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/) discussion board.

## License

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
