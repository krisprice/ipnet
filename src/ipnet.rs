use std;
use std::cmp::{min, max};
use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use emu128::emu128;
use ipext::{ipv6_addr_from_emu128, ipv6_addr_into_emu128, IpAdd, IpSub, IpBitAnd, IpBitOr};
use saturating_shifts::{SaturatingShl, SaturatingShr};

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

// TODO: Not sure if there is a way to do this?
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
    pub fn netmask(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.netmask()),
            IpNet::V6(ref a) => IpAddr::V6(a.netmask()),
        }
    }

    pub fn hostmask(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.hostmask()),
            IpNet::V6(ref a) => IpAddr::V6(a.hostmask()),
        }
    }
    
    pub fn network(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.network()),
            IpNet::V6(ref a) => IpAddr::V6(a.network()),
        }
    }
    
    pub fn broadcast(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.broadcast()),
            IpNet::V6(ref a) => IpAddr::V6(a.broadcast()),
        }
    }
    
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

    pub fn sibling_of(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.sibling_of(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.sibling_of(b),
            (_, _) => false,
        }
    }
}

impl Ipv4Net {
    // TODO: Should new() precompute the netmask, hostmask, network, and
    // broadcast addresses and store these to save recomputing everytime
    // the methods are called?
    // TODO: Should new() truncate the input IpAddr to the prefix_len and
    // store that instead of the supplied address? Technically it doesn't
    // matter, but users may expect that.
    pub fn new(ip: Ipv4Addr, prefix_len: u8) -> Ipv4Net {
        // TODO: Need to implement a proper error handling scheme.
        let prefix_len = if prefix_len > 32 { 32 } else { prefix_len };
        Ipv4Net { addr: ip, prefix_len: prefix_len }
    }

    pub fn netmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(0xffffffffu32.saturating_shl(32 - self.prefix_len))
    }

    pub fn hostmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(0xffffffffu32.saturating_shr(self.prefix_len))
    }

    pub fn network(&self) -> Ipv4Addr {
        self.addr.bitand(0xffffffffu32.saturating_shl(32 - self.prefix_len))
    }

    pub fn broadcast(&self) -> Ipv4Addr {
        self.addr.bitor(0xffffffffu32.saturating_shr(self.prefix_len))
    }

    pub fn supernet(&self) -> Ipv4Net {
        Ipv4Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    // TODO: Should this be an iterator?
    pub fn subnets(&self, new_prefix_len: u8) -> Vec<Ipv4Net> {
        // TODO: Need to implement a proper error handling scheme.
        if new_prefix_len <= self.prefix_len { return Vec::new(); }
        let new_prefix_len = if new_prefix_len > 32 { 32 } else { new_prefix_len };

        let mut network = self.network();
        let broadcast = self.broadcast();
        let step = 2u32.pow(32 - new_prefix_len as u32);
        let mut res: Vec<Ipv4Net> = Vec::new();

        while network <= broadcast {
            res.push(Ipv4Net::new(network, new_prefix_len));
            network = network.saturating_add(step);
        }
        res
    }

    // TODO: Contains should also work for IP addresses.
    pub fn contains(&self, other: &Ipv4Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    pub fn sibling_of(&self, other: &Ipv4Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }
}

// The u128 type would be nice here, but it's not marked stable yet. We
// use an emulated u128 type defined in emu128.rs to make life simpler.
impl Ipv6Net {
    // TODO: Should new() precompute the netmask, hostmask, network, and
    // broadcast addresses and store these to save recomputing everytime
    // the methods are called?
    pub fn new(ip: Ipv6Addr, prefix_len: u8) -> Ipv6Net {
        // TODO: Need to implement a proper error handling scheme.
        let prefix_len = if prefix_len > 128 { 128 } else { prefix_len };
        Ipv6Net { addr: ip, prefix_len: prefix_len }
    }

    pub fn netmask(&self) -> Ipv6Addr {
        ipv6_addr_from_emu128(emu128::max_value().saturating_shl(128 - self.prefix_len))
    }

    pub fn hostmask(&self) -> Ipv6Addr {
        ipv6_addr_from_emu128(emu128::max_value().saturating_shr(self.prefix_len))
    }

    pub fn network(&self) -> Ipv6Addr {
        self.addr.bitand(emu128::max_value().saturating_shl(128 - self.prefix_len))
    }

    // TODO: Technically there is no such thing as a broadcast address
    // in IPv6. Perhaps we should change these method names to first()
    // and last() or start() and end().
    pub fn broadcast(&self) -> Ipv6Addr {
        self.addr.bitor(emu128::max_value().saturating_shr(self.prefix_len))
    }

    pub fn supernet(&self) -> Ipv6Net {
        Ipv6Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    // TODO: Is there a nicer way to do this? Using u128 types would be
    // nice but they're not marked as stable yet. Should this return an
    // iterator instead of a vector?
    pub fn subnets(&self, new_prefix_len: u8) -> Vec<Ipv6Net> {
        // TODO: Need to implement a proper error handling scheme.
        if new_prefix_len <= self.prefix_len { return Vec::new(); }
        let new_prefix_len = if new_prefix_len > 128 { 128 } else { new_prefix_len };

        let mut network = ipv6_addr_into_emu128(self.network());
        let broadcast = ipv6_addr_into_emu128(self.broadcast());

        let step = if new_prefix_len <= 64 {
            emu128 { hi: 1 << (64 - new_prefix_len), lo: 0 }
        }
        else {
            emu128 { hi: 0, lo: 1 << (128 - new_prefix_len) }
        };
        
        let mut res: Vec<Ipv6Net> = Vec::new();
        
        while network <= broadcast {
            res.push(Ipv6Net::new(ipv6_addr_from_emu128(network), new_prefix_len));
            network = network.saturating_add(step);
        }
        res
    }

    // TODO: Contains should also work for IP addresses.
    pub fn contains(&self, other: &Ipv6Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    pub fn sibling_of(&self, other: &Ipv6Net) -> bool {
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

// Generic function for merging any intervals.
fn merge_intervals<T: Copy + Ord>(mut intervals: Vec<(T, T)>) -> Vec<(T, T)> {
    // Sort by (end, start) because we work backwards below.
    intervals.sort_by_key(|k| (k.1, k.0)); 

    // Work backwards from the end of the list to the front.
    let mut i = intervals.len()-1;
    while i >= 1 {
        let (l_start, l_end) = intervals[i-1];
        let (r_start, r_end) = intervals[i];
        
        if r_start <= l_end {
            intervals[i-1].0 = min(l_start, r_start);
            intervals[i-1].1 = max(l_end, r_end);
            intervals.remove(i);
        }
        i -= 1;
    }
    intervals
}

impl IpNet {
    //pub fn aggregate(networks: &Vec<IpNet>) -> Vec<IpNet> {
    //    Vec::new()
    //}
}

impl Ipv4Net {
    // TODO: Will be interesting to experiment with Range types.
    fn interval(&self) -> (u32, u32) {
        (
            u32::from(self.network()),
            u32::from(self.broadcast()).saturating_add(1),
        )
    }

    // EXPERIMENT
    fn next(&self) -> Ipv4Net {
        Ipv4Net::new(Ipv4Addr::from(u32::from(self.network()) + 1u32 << self.prefix_len), self.prefix_len)
    }
    // EXPERIMENT
    fn interval2(&self) -> (Ipv4Addr, Ipv4Addr) {
        (self.network(), self.next().network())
    }

    // TODO: Should this return an iterator instead?
    pub fn aggregate(networks: &Vec<Ipv4Net>) -> Vec<Ipv4Net> {
        let mut intervals: Vec<(_, _)> = networks.iter().map(|n| n.interval()).collect();
        
        intervals = merge_intervals(intervals);
        let mut res: Vec<Ipv4Net> = Vec::new();

        for (start, end) in intervals {
            let mut start = start;
            while start < end {
                let range = end - start;
                let num_bits = 32u32.saturating_sub(range.leading_zeros()).saturating_sub(1);
                let prefix_len = 32 - min(num_bits, start.trailing_zeros());
                res.push(Ipv4Net::new(Ipv4Addr::from(start), prefix_len as u8));
                let step = 2u32.pow(32 - prefix_len);
                start = start.saturating_add(step);
            }
        }
        res
    }
}

impl Ipv6Net {
    // TODO: Will be interesting to experiment with Range types.
    fn interval(&self) -> (emu128, emu128) {
        (
            ipv6_addr_into_emu128(self.network()),
            ipv6_addr_into_emu128(self.broadcast()).saturating_add(emu128 { hi: 0, lo: 1 }),
        )
    }

    // TODO: Should this return an iterator instead?
    pub fn aggregate(networks: &Vec<Ipv6Net>) -> Vec<Ipv6Net> {
        let mut intervals: Vec<(_, _)> = networks.iter().map(|n| n.interval()).collect();

        intervals = merge_intervals(intervals);
        let mut res: Vec<Ipv6Net> = Vec::new();

        // Break up merged intervals into the largest subnets that will fit.
        for (start, end) in intervals {
            let mut start = start;
            while start < end {
                let range = end.saturating_sub(new_start);
                let num_bits = 128u32.saturating_sub(range.leading_zeros()).saturating_sub(1);
                let prefix_len = 128 - min(num_bits, start.trailing_zeros());
                res.push(Ipv6Net::new(ipv6_addr_from_emu128(start), prefix_len as u8));
                let step = if prefix_len <= 64 { emu128 { hi: 1 << (64 - prefix_len), lo: 0 } }
                else { emu128 { hi: 0, lo: 1 << (128 - prefix_len) } };
                start = start.saturating_add(step);
            }
        }
        res
    }
}
