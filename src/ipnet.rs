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
        Ipv4Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    // TODO: Should the parameter be depth, as in the number of
    // divisions to make, or new_prefix_len (self explanatory), or
    // num_subnets? I suspect in use the later two will be more useful.
    // TODO: Should this be an iterator?
    pub fn subnets(&self, new_prefix_len: u8) -> Vec<Ipv4Net> {
        // TODO: Need to test bounds of new_prefix_len and error.
        // Or perhaps just set to 32 in that case.
        // TODO: std::ops::Add missing for Ipv4Addr
        let rng = 2u32.pow(32 - new_prefix_len as u32);
        let mut net = u32::from(self.network());
        let end = u32::from(self.broadcast());
        let mut res: Vec<Ipv4Net> = Vec::new();

        while net < end {
            res.push(Ipv4Net::new(Ipv4Addr::from(net), new_prefix_len));
            net += rng;
        }
        res

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

    pub fn addr(&self) -> Ipv6Addr {
        self.addr
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
        Ipv6Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    // TODO: Is there a nicer way to do this? Using u128 types would be
    // nice but they're not marked as stable yet. Should this return an
    // iterator instead of a vector?
    pub fn subnets(&self, new_prefix_len: u8) -> Vec<Ipv6Net> {
        // TODO: Need to implement a proper error handling scheme.
        if new_prefix_len <= self.prefix_len {
            return Vec::new();
        }

        let mut network = ipv6_addr_into_double_u64(self.network());
        let mut broadcast = ipv6_addr_into_double_u64(self.broadcast());

        let mask = ipv6_addr_into_double_u64(Ipv6Net::new(self.addr.clone(), new_prefix_len).hostmask());

        let mask: [u64; 2] = [
            if new_prefix_len < 64 { 0xffff_ffff_ffff_ffff >> new_prefix_len } else { 0x0 },
            if new_prefix_len >= 64 && new_prefix_len < 128 { 0xffff_ffff_ffff_ffff >> new_prefix_len - 64 } else { 0x0 }
        ];

        let mut res: Vec<Ipv6Net> = Vec::new();

        while network < broadcast {
            res.push(Ipv6Net::new(ipv6_addr_from_double_u64(network), new_prefix_len));
            
            network[0] |= mask[0];
            network[1] |= mask[1];

            let (lo, ov) = network[1].overflowing_add(1);
            network[1] = lo;
            
            if ov {
                network[0] += 1;
            }
        }

        res
    }

    pub fn contains(&self, other: &Ipv6Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    pub fn sibling(&self, other: &Ipv6Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }
}

// TODO: It would be nice to implement From on Ipv6Addr for this.
pub fn ipv6_addr_from_double_u64(segments: [u64; 2]) -> Ipv6Addr {
    let (hi, lo) = (segments[0], segments[1]);
    Ipv6Addr::new(
        (hi >> 48) as u16, (hi >> 32) as u16, (hi >> 16) as u16, hi as u16,
        (lo >> 48) as u16, (lo >> 32) as u16, (lo >> 16) as u16, lo as u16
    )
}

// TODO: It would be nice to implement From on Ipv6Addr for this.
pub fn ipv6_addr_into_double_u64(ip: Ipv6Addr) -> [u64; 2] {
    let ip = ip.octets();
    [
        ((ip[0] as u64) << 56) + ((ip[1] as u64) << 48) +
        ((ip[2] as u64) << 40) + ((ip[3] as u64) << 32) +
        ((ip[4] as u64) << 24) + ((ip[5] as u64) << 16) +
        ((ip[6] as u64) << 8) + (ip[7] as u64),
        ((ip[8] as u64) << 56) + ((ip[9] as u64) << 48) +
        ((ip[10] as u64) << 40) + ((ip[11] as u64) << 32) +
        ((ip[12] as u64) << 24) + ((ip[13] as u64) << 16) +
        ((ip[14] as u64) << 8) + (ip[15] as u64), 
    ]
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
