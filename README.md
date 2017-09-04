Nearing 1.0 release, feedback and code reviews are very welcome. Open an issue or comment here on the [Reddit post](https://www.reddit.com/r/rust/comments/6xk3jh/first_crate_ipnet_types_and_methods_for_network/).

This module provides types and methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. It only uses stable Rust features so it compiles using the stable toolchain. And its design aligns to the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types provided in the Rust standard library.

The module includes extension traits to provide Add, Sub, BitAnd, and BitOr operations to `Ipv4Addr` and `Ipv6Addr`.

Available on [Crates.io] and read the [documentation] for the full details.

[Crates.io]: https://crates.io/crates/ipnet
[documentation]: https://docs.rs/ipnet/

## TODO / Open Questions:

* Should `IpNet::new()` truncate the input `IpAddr` to the prefix_len and store that instead? Users may expect one behavior over the other. Truncating it at creation time means that the provided address can't be returned if the user has a need for it, and sort behaviour won't be influenced by it. Though we don't have a way to access it as the field is not public there is no `address()` method, this could be added. There is a `trunc()` method that does truncate the network, but chaining `IpNet::new().trunc()` or `IpNet::from().unwrap().trunc()` is kind of ugly. I am leaning towards changing this behaviour so the address is truncated at creation, then in future if Rust provides default args having a default `truncate=true` argument that users can override if they don't want it truncated.
* Perhaps this should be solved with a `new_with_trunc()` constructor method. Or perhaps a series of (builder methods)[https://rust-lang-nursery.github.io/api-guidelines/type-safety.html#non-consuming-builders-preferred]?
* Should prefix_len be it's own type? This seems like newtype overload, but the API guidelines would tend to indicate it (should be)[https://rust-lang-nursery.github.io/api-guidelines/dependability.html].
* The guidelines suggest `subnets()` and `hosts()` should return an iterator type `Subnets` and `Hosts` respectively rather than the generic `IpNetIter<T>` they currently return. See (here)[https://rust-lang-nursery.github.io/api-guidelines/naming.html#iterator-type-names-match-the-methods-that-produce-them-c-iter-ty].

## Future

* Explore representing the results of methods such as hosts() and subnets() as a Range. This requires both the Add and Step traits be implemented on the target type. For the three IpAddr types implementing Add must be done through an enhancement to the standard library. For all types, using Step means we must use nightly because it is not yet stable. This crate only uses stable Rust features.
* Can we implement the std::ops::{Add, Sub, BitAnd, BitOr} traits for Ipv4Addr and Ipv6Addr in the standard library? These are common operations on IP addresses. I've started a thread on this over on [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/).

## Legal

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
