[![Build Status](https://travis-ci.org/krisprice/ipnet.svg?branch=master)](https://travis-ci.org/krisprice/ipnet)

This module provides types and useful methods for working with IPv4 and IPv6 network addresses, commonly called IP prefixes. The new `IpNet`, `Ipv4Net`, and `Ipv6Net` types build on the existing `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` types already provided in Rust's standard library and align to their design to stay consistent.

The module also provides types for iterating over IP address ranges, and useful traits that extend `Ipv4Addr` and `Ipv6Addr` with methods for addition, subtraction, bitwise-and, and bitwise-or operations that are missing in Rust's standard library.

The module only uses stable features so it is guaranteed to compile using the stable toolchain. Tests aim for thorough coverage and can be found in both the test modules and doctests. Please file an [issue on GitHub] if you have any problems, requests, or suggested improvements.

Read the [documentation] for the full details. And find it on [Crates.io].

[documentation]: https://docs.rs/ipnet/
[Crates.io]: https://crates.io/crates/ipnet
[issue on GitHub]: https://github.com/krisprice/ipnet/issues

## Release 2.0 requirements

Release 2.0 requires Rust version 1.26 or later. The prior release of this library provided an emulated 128 bit integer module to support IPv6 addresses. This has been replaced with Rust's built-in 128 bit integer support now that it is stable. There may be issues with Rust's 128 bit integer support on some targets (e.g. Emscripten). Please continue to use the prior release if you have any issues with Rust's 128 bit integer support on your chosen target.

## Examples

Create a network address and print the hostmask:

```rust
extern crate ipnet;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use ipnet::{IpNet, Ipv4Net, Ipv6Net};

fn main() {
    // Create an Ipv4Net and Ipv6Net from their constructors

    let net4 = Ipv4Net::new(Ipv4Addr::new(10, 1, 1, 0), 24).unwrap();
    let net6 = Ipv6Net::new(Ipv6Addr::new(0xfd, 0, 0, 0, 0, 0, 0, 0), 24).unwrap();

    // They can also be created from string representations

    let net4 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
    let net6 = Ipv6Net::from_str("fd00::/24").unwrap();

    // Or alternatively as
    
    let net4: Ipv4Net = "10.1.1.0/24".parse().unwrap();
    let net6: Ipv6Net = "fd00::/24".parse().unwrap();

    // IpNet can represent either an IPv4 or IPv6 network address

    let net = IpNet::from(net4);
    
    // It can also be created from string representations

    let net: IpNet = "fd00::/24".parse().unwrap();

    // The hostmask and more can be obtained using the methods found on
    // the IpNet types

    println!("net is {} and it's hostmask is: {}", net, net.hostmask());
    println!("net4 is {} and it's hostmask is: {}", net4, net4.hostmask());
    println!("net6 is {} and it's hostmask is: {}", net6, net6.hostmask());
}
```

Iterate over the valid subnets between two IPv4 addresses:

```rust
extern crate ipnet;
use std::net::Ipv4Addr;
use ipnet::Ipv4Subnets;

fn main() {
    let start = Ipv4Addr::new(10, 0, 0, 0);
    let end = Ipv4Addr::new(10, 0, 0, 239);

    // Output all subnets starting with the largest that will fit.
    //
    // Outputs:
    // subnet 0: 10.0.0.0/25
    // subnet 1: 10.0.0.128/26
    // subnet 2: 10.0.0.192/27
    // subnet 3: 10.0.0.224/28

    let subnets = Ipv4Subnets::new(start, end, 0);

    for (i, n) in subnets.enumerate() {
        println!("subnet {}: {}", i, n);
    }
 
    // Output all subnets with prefix lengths less than or equal to 26.
    //
    // Outputs:
    // subnet 0: 10.0.0.0/26
    // subnet 1: 10.0.0.64/26
    // subnet 2: 10.0.0.128/26
    // subnet 3: 10.0.0.192/27
    // subnet 4: 10.0.0.224/28

    let subnets = Ipv4Subnets::new(start, end, 26);

    for (i, n) in subnets.enumerate() {
        println!("subnet {}: {}", i, n);
    }
}
```

Aggregate a list of IP prefixes:

```rust
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

    let nets: Vec<IpNet> = strings.iter().filter_map(|p| p.parse().ok()).collect();
    
    println!("\nInput IP prefix list:");
    
    for n in &nets {
        println!("{}", n);
    }
    
    println!("\nAggregated IP prefixes:");
    
    for n in IpNet::aggregate(&nets) {
        println!("{}", n);
    }
}
```

## Future

* Implementing `std::ops::{Add, Sub, BitAnd, BitOr}` for `Ipv4Addr` and `Ipv6Addr` would be useful as these are common operations on IP addresses. If done, the extension traits provided in this module would be removed and the major version incremented. Implementing these requires a change to the standard library. I've started a thread on this topic on the [Rust Internals](https://internals.rust-lang.org/t/pre-rfc-implementing-add-sub-bitand-bitor-for-ipaddr-ipv4addr-ipv6addr/) discussion board.
* The results of `hosts()` and potentially `subnets()` should be represented as a `Range` rather than the custom `IpAddrRange` and `IpSubnets` types provided in this module. This requires the target types to have `Add` and `Step` implemented for them. Implementing `Add` for `IpAddr`, `Ipv4Addr`, and `Ipv6Addr` requires a change to the standard library (see above). And `Step` is still unstable so exploring this will also wait until it has stablized.

## License

Copyright (c) 2017, Juniper Networks, Inc. All rights reserved.

This code is licensed to you under either the MIT License or Apache License, Version 2.0 at your choice (the "License"). You may not use this code except in compliance with the License. This code is not an official Juniper product. You can obtain a copy of the License at: https://opensource.org/licenses/MIT or http://www.apache.org/licenses/LICENSE-2.0
