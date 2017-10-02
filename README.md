[![Build Status](https://travis-ci.org/krisprice/ipnet.svg?branch=master)](https://travis-ci.org/krisprice/ipnet)

This module provides types and useful methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. The new `IpNet`, `Ipv4Net`, and `Ipv6Net` types build on the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types already provided in Rust's standard library and align to their design to stay consistent. The module also provides types for iterating over IP address ranges, and useful traits that extend `Ipv4Addr` and `Ipv6Addr` with methods for addition, subtraction, bitwise-and, and bitwise-or operations that are missing in Rust's standard library.

The module only uses stable feature so it is guaranteed to compile using the stable toolchain. Tests aim for thorough coverage and can be found in both the test modules and doctests. Please file an [issue on GitHub] if you have any problems, requests, or suggested improvements.

Read the [documentation] for the full details. And find it on [Crates.io].

[documentation]: https://docs.rs/ipnet/
[Crates.io]: https://crates.io/crates/ipnet
[issue on GitHub]: https://github.com/krisprice/ipnet/issues

## Examples

Aggregate a list of prefixes.

```
extern crate ipnet;
use ipnet::IpNet;

fn main() {
    let strings = vec![
        "10.0.0.0/24", "10.0.1.0/24", "10.0.1.1/24", "10.0.1.2/24",
        "10.0.2.0/24",
        "10.1.0.0/24", "10.1.1.0/24",
        "192.168.0.0/24", "192.168.1.0/24", "192.168.2.0/24", "192.168.3.0/24",
        "fd00::/32", "fd00:1::/32",
    ];

    let ipnets: Vec<IpNet> = strings.iter().filter_map(|p| p.parse().ok()).collect();
    
    println!("\nInput IP prefix list:");
    
    for n in &ipnets {
        println!("{}", n);
    }
    
    println!("\nAggregated IP prefixes:");
    
    for n in IpNet::aggregate(&ipnets) {
        println!("{}", n);
    }
}
```

## Future

* When `u128` is stablized it will replace `Emu128` and the major version will be incremented.
* Implementing `std::ops::{Add, Sub, BitAnd, BitOr}` for `Ipv4Addr` and `Ipv6Addr` would be useful as these are common operations on IP addresses. If done, the extension traits provided in this module would be removed and the major version incremented. Implementing these requires a change to the standard library. I've started a thread on this topic on the [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/) discussion board.
* The results of `hosts()` and potentially `subnets()` should be represented as a `Range` rather than the custom `IpAddrRange` and `IpSubnets` types provided in this module. This requires the target types to have `Add` and `Step` implemented for them. Implementing `Add` for `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` requires a change to the standard library (see above). And `Step` is still unstable so exploring this will also wait until it has stablized.

## License

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under the Apache License, Version 2.0 (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: http://www.apache.org/licenses/LICENSE-2.0
