use core::net::{Ipv4Addr, Ipv6Addr};

use super::{
    IpAddrRange, IpNet, IpSubnets, Ipv4AddrRange, Ipv4Net, Ipv4Subnets, Ipv6AddrRange, Ipv6Net,
    Ipv6Subnets,
};

use quickcheck::{Arbitrary, Gen};

const MAX_IPV4_PREFIX_SIZE: u8 = 32;
const MAX_IPV6_PREFIX_SIZE: u8 = 128;

impl Arbitrary for IpNet {
    fn arbitrary(g: &mut Gen) -> Self {
        if bool::arbitrary(g) {
            Ipv4Net::arbitrary(g).into()
        } else {
            Ipv6Net::arbitrary(g).into()
        }
    }
}

impl Arbitrary for Ipv4Net {
    fn arbitrary(g: &mut Gen) -> Self {
        let addr = Ipv4Addr::arbitrary(g);
        let prefix = u8::arbitrary(g) % (MAX_IPV4_PREFIX_SIZE + 1);
        Ipv4Net::new_assert(addr, prefix)
    }
}

impl Arbitrary for Ipv6Net {
    fn arbitrary(g: &mut Gen) -> Self {
        let addr = Ipv6Addr::arbitrary(g);
        let prefix = u8::arbitrary(g) % (MAX_IPV6_PREFIX_SIZE + 1);
        Ipv6Net::new_assert(addr, prefix)
    }
}

impl Arbitrary for IpSubnets {
    fn arbitrary(g: &mut Gen) -> Self {
        if bool::arbitrary(g) {
            Ipv4Subnets::arbitrary(g).into()
        } else {
            Ipv6Subnets::arbitrary(g).into()
        }
    }
}

impl Arbitrary for Ipv4Subnets {
    fn arbitrary(g: &mut Gen) -> Self {
        let start = Ipv4Addr::arbitrary(g);
        let end = Ipv4Addr::arbitrary(g);
        let prefix = u8::arbitrary(g) % (MAX_IPV4_PREFIX_SIZE + 1);
        Ipv4Subnets::new(start, end, prefix)
    }
}

impl Arbitrary for Ipv6Subnets {
    fn arbitrary(g: &mut Gen) -> Self {
        let start = Ipv6Addr::arbitrary(g);
        let end = Ipv6Addr::arbitrary(g);
        let prefix = u8::arbitrary(g) % (MAX_IPV6_PREFIX_SIZE + 1);
        Ipv6Subnets::new(start, end, prefix)
    }
}

impl Arbitrary for IpAddrRange {
    fn arbitrary(g: &mut Gen) -> Self {
        if bool::arbitrary(g) {
            Ipv4AddrRange::arbitrary(g).into()
        } else {
            Ipv6AddrRange::arbitrary(g).into()
        }
    }
}

impl Arbitrary for Ipv4AddrRange {
    fn arbitrary(g: &mut Gen) -> Self {
        let start = Ipv4Addr::arbitrary(g);
        let end = Ipv4Addr::arbitrary(g);
        Ipv4AddrRange::new(start, end)
    }
}

impl Arbitrary for Ipv6AddrRange {
    fn arbitrary(g: &mut Gen) -> Self {
        let start = Ipv6Addr::arbitrary(g);
        let end = Ipv6Addr::arbitrary(g);
        Ipv6AddrRange::new(start, end)
    }
}
