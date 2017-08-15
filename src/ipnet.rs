use std;
use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub enum IpNet {
    V4(Ipv4Net),
    V6(Ipv6Net),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub struct Ipv4Net {
    addr: Ipv4Addr,
    prefix_len: u8,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub struct Ipv6Net {
    addr: Ipv6Addr,
    prefix_len: u8,
}

// For the time being deref method calls to the IpAddr implemenations.

/*impl std::ops::Deref for IpNet {
    type Target = IpAddr;
    fn deref(&self) -> &Self::Target {
        match *self {
            IpNet::V4(ref a) => a.addr,
            IpNet::V6(ref a) => a.addr,
        }
    }
}*/

impl std::ops::Deref for Ipv4Net {
    type Target = Ipv4Addr;
    fn deref(&self) -> &Self::Target {
        &self.addr
    }
}

impl std::ops::Deref for Ipv6Net {
    type Target = Ipv6Addr;
    fn deref(&self) -> &Self::Target {
        &self.addr
    }
}

impl IpNet {
    pub fn supernet(&self) -> IpNet {
        match *self {
            IpNet::V4(ref a) => IpNet::V4(a.supernet()),
            IpNet::V6(ref a) => IpNet::V6(a.supernet()),
        }
    }

    pub fn contains(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.contains(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.contains(b),
            (_, _) => false,
        }
    }

    pub fn sibling(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.sibling(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.sibling(b),
            (_, _) => false,
        }
    }
}

impl Ipv4Net {
    pub fn new(ip: Ipv4Addr, prefix_len: u8) -> Ipv4Net {
        // TODO: Should error if prefix_len > 32 as prefix_len <= 32 is
        // assumed in subsequent methods.
        Ipv4Net { addr: ip, prefix_len: prefix_len, }
    }

    pub fn netmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(
            // Avoid deny(exceeding_bitshifts)
            if self.prefix_len > 0 {
                0xffffffff << 32 - self.prefix_len
            }
            else {
                0x00000000
            }
        )
    }

    pub fn hostmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(
            // Avoid deny(exceeding_bitshifts)
            if self.prefix_len < 32 {
                0xffffffff >> self.prefix_len
            }
            else {
                0x00000000
            } 
        )
    }

    pub fn network(&self) -> Ipv4Addr {
        // BitAnd is not implemented for Ipv4Addr.
        Ipv4Addr::from(u32::from(self.addr) & u32::from(self.netmask()))
    }

    pub fn broadcast(&self) -> Ipv4Addr {
        // BitOr is not implemented for Ipv4Addr.
        Ipv4Addr::from(u32::from(self.addr) | u32::from(self.hostmask()))
    }

    pub fn supernet(&self) -> Ipv4Net {
        Ipv4Net::new(Ipv4Addr::from(self.octets()), self.prefix_len - 1)
    }

    pub fn contains(&self, other: &Ipv4Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    pub fn sibling(&self, other: &Ipv4Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }
}

impl Ipv6Net {
    pub fn new(ip: Ipv6Addr, prefix_len: u8) -> Ipv6Net {
        // TODO: Should error if prefix_len > 128 as prefix_len <= 128
        // is assumed in subsequent methods.
        Ipv6Net { addr: ip, prefix_len: prefix_len, }
    }

    // The u128 type would be nice here, but it's not marked stable yet.
    pub fn netmask(&self) -> Ipv6Addr {
        // Avoid deny(exceeding_bitshifts)
        let a: u64 = if self.prefix_len > 0 { 0xffff_ffff_ffff_ffff << 64u8.saturating_sub(self.prefix_len) } else { 0x0 };
        let b: u64 = if self.prefix_len > 64 { 0xffff_ffff_ffff_ffff << 128 - self.prefix_len } else { 0x0 };
        
        Ipv6Addr::new(
            (a >> 48) as u16, (a >> 32) as u16, (a >> 16) as u16, a as u16,
            (b >> 48) as u16, (b >> 32) as u16, (b >> 16) as u16, b as u16
        )
    }

    // The u128 type would be nice here, but it's not marked stable yet.
    pub fn hostmask(&self) -> Ipv6Addr {
        // Avoid deny(exceeding_bitshifts)
        let a: u64 = if self.prefix_len < 64 { 0xffff_ffff_ffff_ffff >> self.prefix_len } else { 0x0 };
        let b: u64 = if self.prefix_len < 128 { 0xffff_ffff_ffff_ffff >> self.prefix_len.saturating_sub(64) } else { 0x0 };
        
        Ipv6Addr::new(
            (a >> 48) as u16, (a >> 32) as u16, (a >> 16) as u16, a as u16,
            (b >> 48) as u16, (b >> 32) as u16, (b >> 16) as u16, b as u16
        )
    }

    // The u128 type would be nice here, but it's not marked stable yet.
    pub fn network(&self) -> Ipv6Addr {
        // BitAnd is not implemented for Ipv6Addr.
        let ip = self.segments();
        let m = self.netmask().segments();

        Ipv6Addr::new(
            ip[0] & m[0], ip[1] & m[1], ip[2] & m[2], ip[3] & m[3],
            ip[4] & m[4], ip[5] & m[5], ip[6] & m[6], ip[7] & m[7]
        )
    }

    // TODO: Technically there is no such thing as a broadcast. Perhaps
    // we should change the network() and broadcast() methods to be
    // first() and last() or similar.
    // The u128 type would be nice here, but it's not marked stable yet.
    pub fn broadcast(&self) -> Ipv6Addr {
        // BitOr is not implemented for Ipv4Addr.
        let ip = self.segments();
        let m = self.hostmask().segments();

        Ipv6Addr::new(
            ip[0] | m[0], ip[1] | m[1], ip[2] | m[2], ip[3] | m[3],
            ip[4] | m[4], ip[5] | m[5], ip[6] | m[6], ip[7] | m[7]
        )
    }

    pub fn supernet(&self) -> Ipv6Net {
        Ipv6Net::new(Ipv6Addr::from(self.segments()), self.prefix_len - 1)
    }

    pub fn contains(&self, other: &Ipv6Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    pub fn sibling(&self, other: &Ipv6Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }
}

impl fmt::Display for IpNet {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            IpNet::V4(ref a) => a.fmt(fmt),
            IpNet::V6(ref a) => a.fmt(fmt),
        }
    }
}

impl fmt::Display for Ipv4Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.addr, self.prefix_len)
    }
}

impl fmt::Display for Ipv6Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.addr, self.prefix_len)
    }
}

#[cfg(test)]
mod tests {
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    use std::option::Option::{Some, None};
    use std::str::FromStr;
    use ipnet::{IpNet, Ipv4Net, Ipv6Net};
    
    #[test]
    fn test_ipv4_net() {
        // TODO: Test the boundaries (/0, /32, /64, /128). Or iterate
        // over every bit.
        assert_eq!(
            IpNet::from_str("10.0.0.0/8").unwrap(),
            IpNet::V4(Ipv4Net { addr: Ipv4Addr::from_str("10.0.0.0").unwrap(), prefix_len: 8 })
        );
        assert_eq!(
            Ipv4Net::from_str("172.16.0.0/12").unwrap(),
            Ipv4Net { addr: Ipv4Addr::from_str("172.16.0.0").unwrap(), prefix_len: 12 }
        );
        assert_eq!(
            Ipv4Net::from_str("172.16.0.0/12").unwrap().netmask(),
            Ipv4Addr::from_str("255.240.0.0").unwrap()
        );
        assert_eq!(
            Ipv4Net::from_str("172.16.0.0/12").unwrap().hostmask(),
            Ipv4Addr::from_str("0.15.255.255").unwrap()
        );
        assert_eq!(
            Ipv4Net::from_str("172.16.0.0/12").unwrap().network(),
            Ipv4Addr::from_str("172.16.0.0").unwrap()
        );
        assert_eq!(
            Ipv4Net::from_str("172.16.0.0/12").unwrap().broadcast(),
            Ipv4Addr::from_str("172.31.255.255").unwrap()
        );
    }
}
