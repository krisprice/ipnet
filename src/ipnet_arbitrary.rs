use core::net::{Ipv4Addr, Ipv6Addr};

use super::{
    IpAddrRange, IpNet, IpSubnets, Ipv4AddrRange, Ipv4Net, Ipv4Subnets, Ipv6AddrRange, Ipv6Net,
    Ipv6Subnets,
};

use arbitrary::{Arbitrary, Unstructured};

const MAX_IPV4_PREFIX_SIZE: u8 = 32;
const MAX_IPV6_PREFIX_SIZE: u8 = 128;

impl<'a> Arbitrary<'a> for IpNet {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        if u.arbitrary()? {
            Ipv4Net::arbitrary(u).map(Into::into)
        } else {
            Ipv6Net::arbitrary(u).map(Into::into)
        }
    }
}

impl<'a> Arbitrary<'a> for Ipv4Net {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let addr = Ipv4Addr::arbitrary(u)?;
        let prefix = u.int_in_range(0..=MAX_IPV4_PREFIX_SIZE)?;
        Ok(Ipv4Net::new_assert(addr, prefix))
    }
}

impl<'a> Arbitrary<'a> for Ipv6Net {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let addr = Ipv6Addr::arbitrary(u)?;
        let prefix = u.int_in_range(0..=MAX_IPV6_PREFIX_SIZE)?;
        Ok(Ipv6Net::new_assert(addr, prefix))
    }
}

impl<'a> Arbitrary<'a> for IpSubnets {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        if u.arbitrary()? {
            Ipv4Subnets::arbitrary(u).map(Into::into)
        } else {
            Ipv6Subnets::arbitrary(u).map(Into::into)
        }
    }
}

impl<'a> Arbitrary<'a> for Ipv4Subnets {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = Ipv4Addr::arbitrary(u)?;
        let end = Ipv4Addr::arbitrary(u)?;
        let prefix = u.int_in_range(0..=MAX_IPV4_PREFIX_SIZE)?;
        Ok(Ipv4Subnets::new(start, end, prefix))
    }
}

impl<'a> Arbitrary<'a> for Ipv6Subnets {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = Ipv6Addr::arbitrary(u)?;
        let end = Ipv6Addr::arbitrary(u)?;
        let prefix = u.int_in_range(0..=MAX_IPV6_PREFIX_SIZE)?;
        Ok(Ipv6Subnets::new(start, end, prefix))
    }
}

impl<'a> Arbitrary<'a> for IpAddrRange {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        if u.arbitrary()? {
            Ipv4AddrRange::arbitrary(u).map(Into::into)
        } else {
            Ipv6AddrRange::arbitrary(u).map(Into::into)
        }
    }
}

impl<'a> Arbitrary<'a> for Ipv4AddrRange {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = Ipv4Addr::arbitrary(u)?;
        let end = Ipv4Addr::arbitrary(u)?;
        Ok(Ipv4AddrRange::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for Ipv6AddrRange {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = Ipv6Addr::arbitrary(u)?;
        let end = Ipv6Addr::arbitrary(u)?;
        Ok(Ipv6AddrRange::new(start, end))
    }
}
