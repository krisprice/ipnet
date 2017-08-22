use std;
use std::cmp::{min, max};
use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use emu128::Emu128;
use ipext::{IpAdd, IpBitAnd, IpBitOr};
use saturating_shifts::{SaturatingShl, SaturatingShr};

/// An IP network address, either IPv4 or IPv6.
///
/// This enum can contain either an [`Ipv4Net`] or an [`Ipv6Net`], see their
/// respective documentation for more details.
///
/// [`Ipv4Net`]: struct.Ipv4Addr.html
/// [`Ipv6Net`]: struct.Ipv6Addr.html
///
/// # Examples
///
/// ```
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
/// use ipnet::{IpNet, Ipv4Net, Ipv6Net};
/// use std::str::FromStr;
///
/// let net_v4 = IpNet::from_str("10.1.1.0/24").unwrap();
/// let net_v6 = IpNet::from_str("fd00::/32").unwrap();
/// 
/// assert_eq!("10.1.1.0".parse(), Ok(net_v4.network()));
/// assert_eq!("fd00::".parse(), Ok(net_v6.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub enum IpNet {
    V4(Ipv4Net),
    V6(Ipv6Net),
}

/// An IPv4 network address.
///
/// See [`IpNet`] for a type encompassing both IPv4 and IPv6 network
/// addresses.
///
/// [`IpNet`]: enum.IpAddr.html
///
/// # Textual representation
///
/// `Ipv4Net` provides a [`FromStr`] implementation.  This is represented
/// using the `FromStr` implementation for `Ipv4Addr` followed by a `/`
/// character and the prefix length in decimal. See [RFC 3632] for the
/// CIDR notation.
///
/// [RFC 4632]: https://tools.ietf.org/html/rfc4632
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
///
/// # Examples
///
/// ```
/// //TODO
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub struct Ipv4Net {
    addr: Ipv4Addr,
    prefix_len: u8,
}

/// An IPv6 network address.
///
/// See [`IpNet`] for a type encompassing both IPv4 and IPv6 network
/// addresses.
///
/// [`IpNet`]: enum.IpAddr.html
///
/// # Textual representation
///
/// `Ipv6Net` provides a [`FromStr`] implementation. This is represented
/// using the `FromStr` implementation for `Ipv6Addr` followed by a `/`
/// character and the prefix length in decimal. See [RFC 3632] for the
/// CIDR notation.
///
/// [RFC 4632]: https://tools.ietf.org/html/rfc4632
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
///
/// # Examples
///
/// ```
/// //TODO
/// ```
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
    ///
    ///
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

    /// Creates a new IPv4 network address from an `Ipv4Addr` and prefix
    /// length.
    
    /// # TODO
    /// * Should new() truncate the input Ipv4Addr to the prefix_len and
    ///   store that instead? Technically it doesn't matter, but users
    ///   may expect one behavior over the other.
    /// * Should new() precompute the netmask, hostmask, network, and
    ///   broadcast addresses and store these to avoid recomputing
    ///   everytime the methods are called?
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::new(Ipv4Addr::new(10, 1, 1, 0), 24);
    /// ```
    pub fn new(ip: Ipv4Addr, prefix_len: u8) -> Ipv4Net {
        // TODO: Need to implement a proper error handling scheme.
        let prefix_len = if prefix_len > 32 { 32 } else { prefix_len };
        Ipv4Net { addr: ip, prefix_len: prefix_len }
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.netmask(), Ipv4Addr::from_str("255.255.240.0").unwrap());
    /// ```
    pub fn netmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(0xffffffffu32.saturating_shl(32 - self.prefix_len))
    }

    /// Returns the network address. Truncates the provided Ipv6Addr to
    /// the prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.hostmask(), Ipv4Addr::from_str("0.0.15.255").unwrap());
    /// ```
    pub fn hostmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(0xffffffffu32.saturating_shr(self.prefix_len))
    }

    pub fn network(&self) -> Ipv4Addr {
        self.addr.bitand(0xffffffffu32.saturating_shl(32 - self.prefix_len))
    }

    /// Returns the broadcast address. Returns the provided Ipv4Addr
    /// with all bits after the prefix length set.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::from_str("172.16.0.0/22").unwrap();
    /// assert_eq!(net.broadcast(), Ipv4Addr::from_str("172.16.3.255").unwrap());
    /// ```
    pub fn broadcast(&self) -> Ipv4Addr {
        self.addr.bitor(0xffffffffu32.saturating_shr(self.prefix_len))
    }

    /// Returns the `Ipv4Net` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::from_str("172.16.1.0/24").unwrap();
    /// assert_eq!(net.supernet().network(), Ipv4Addr::from_str("172.16.0.0").unwrap());
    /// ```
    pub fn supernet(&self) -> Ipv4Net {
        Ipv4Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    /// Returns the subnets of this network at the given prefix length.
    ///
    /// TODO:
    /// * Should this return an iterator instead of a vector?
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net = Ipv4Net::from_str("10.1.0.0/16").unwrap();
    /// assert_eq!(net.subnets(18), vec![
    ///     Ipv4Net::from_str("10.1.0.0/18").unwrap(),
    ///     Ipv4Net::from_str("10.1.64.0/18").unwrap(),
    ///     Ipv4Net::from_str("10.1.128.0/18").unwrap(),
    ///     Ipv4Net::from_str("10.1.192.0/18").unwrap(),
    /// ]);
    /// ```
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

    /// Returns `true` if this network contains the given network.
    ///
    /// TODO:
    /// * Contains should also work for IP addresses.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net1 = Ipv4Net::from_str("10.1.0.0/16").unwrap();
    /// let net2 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
    /// assert!(net1.contains(&net2));
    /// ```
    // TODO: Contains should also work for IP addresses.
    pub fn contains(&self, other: &Ipv4Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }
    
    /// Returns `true` if this network and the given network are both in
    /// the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv4Net;
    ///
    /// let net1 = Ipv4Net::from_str("10.1.0.0/24").unwrap();
    /// let net2 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
    /// let net3 = Ipv4Net::from_str("10.1.2.0/24").unwrap();
    /// assert!(net1.sibling_of(&net2));
    /// assert!(!net2.sibling_of(&net3));
    /// ```
    pub fn sibling_of(&self, other: &Ipv4Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }
}

// The u128 type would be nice here, but it's not marked stable yet. We
// use an emulated u128 type defined in Emu128.rs to make life simpler.
impl Ipv6Net {    
    /// Creates a new IPv4 network address from an `Ipv4Addr` and prefix
    /// length.
    ///
    /// # TODO
    /// * Should new() truncate the input Ipv6Addr to the prefix_len and
    ///   store that instead? Technically it doesn't matter, but users
    ///   may expect one behavior over the other.
    /// * Should new() precompute the netmask, hostmask, network, and
    ///   broadcast addresses and store these to avoid recomputing
    ///   everytime the methods are called?
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::new(Ipv6Addr::from_str("fd00::").unwrap(), 24);
    /// ```
    pub fn new(ip: Ipv6Addr, prefix_len: u8) -> Ipv6Net {
        // TODO: Need to implement a proper error handling scheme.
        let prefix_len = if prefix_len > 128 { 128 } else { prefix_len };
        Ipv6Net { addr: ip, prefix_len: prefix_len }
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::from_str("fd00::/24").unwrap();
    /// assert_eq!(net.netmask(), Ipv6Addr::from_str("ffff:ff00::").unwrap());
    /// ```
    pub fn netmask(&self) -> Ipv6Addr {
        Emu128::max_value().saturating_shl(128 - self.prefix_len).into()
    }

    /// Returns the host mask.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::from_str("fd00::/24").unwrap();
    /// assert_eq!(net.hostmask(), Ipv6Addr::from_str("::ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap());
    /// ```
    pub fn hostmask(&self) -> Ipv6Addr {
        Emu128::max_value().saturating_shr(self.prefix_len).into()
    }

    /// Returns the network address. Truncates the provided Ipv6Addr to
    /// the prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::new(Ipv6Addr::from_str("fd00:1234:5678::").unwrap(), 24);
    /// assert_eq!(net.network(), Ipv6Addr::from_str("fd00:1200::").unwrap());
    /// ```
    pub fn network(&self) -> Ipv6Addr {
        self.addr.bitand(Emu128::max_value().saturating_shl(128 - self.prefix_len))
    }
    
    /// Returns the broadcast address. Returns the provided Ipv6Addr
    /// with all bits after the prefix length set.
    ///
    /// # TODO
    /// * Technically there is no such thing as a broadcast address in
    ///   in IPv6. Perhaps we should change the methods to first() and
    ///   last() or start() and end().
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::from_str("fd00:1234:5678::/24").unwrap();
    /// assert_eq!(net.broadcast(), Ipv6Addr::from_str("fd00:12ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap());
    /// ```
    pub fn broadcast(&self) -> Ipv6Addr {
        self.addr.bitor(Emu128::max_value().saturating_shr(self.prefix_len))
    }

    /// Returns the `Ipv6Net` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::from_str("fd00:ff00::/24").unwrap();
    /// assert_eq!(net.supernet().network(), Ipv6Addr::from_str("fd00:fe00::").unwrap());
    /// ```
    pub fn supernet(&self) -> Ipv6Net {
        Ipv6Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    /// Returns the subnets of this network at the given prefix length.
    ///
    /// TODO:
    /// * Is there a nicer way to do this? Using u128 types would be
    ///   nice but they're not marked as stable yet.
    /// * Should this return an iterator instead of a vector?
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net = Ipv6Net::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(18), vec![
    ///     Ipv6Net::from_str("fd00::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:4000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:8000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:c000::/18").unwrap(),
    /// ]);
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> Vec<Ipv6Net> {
        // TODO: Need to implement a proper error handling scheme.
        if new_prefix_len <= self.prefix_len { return Vec::new(); }
        let new_prefix_len = if new_prefix_len > 128 { 128 } else { new_prefix_len };

        let mut network = Emu128::from(self.network());
        let broadcast = Emu128::from(self.broadcast());

        let step = if new_prefix_len <= 64 {
            Emu128 { hi: 1 << (64 - new_prefix_len), lo: 0 }
        }
        else {
            Emu128 { hi: 0, lo: 1 << (128 - new_prefix_len) }
        };
        
        let mut res: Vec<Ipv6Net> = Vec::new();
        
        while network <= broadcast {
            res.push(Ipv6Net::new(network.into(), new_prefix_len));
            network = network.saturating_add(step);
        }
        res
    }

    /// Returns `true` if this network contains the given network.
    ///
    /// TODO:
    /// * Contains should also work for IP addresses.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net1 = Ipv6Net::from_str("fd00::/16").unwrap();
    /// let net2 = Ipv6Net::from_str("fd00::/17").unwrap();
    /// assert!(net1.contains(&net2));
    /// ```
    pub fn contains(&self, other: &Ipv6Net) -> bool {
        self.network() <= other.network() && self.broadcast() >= other.broadcast()
    }

    /// Returns `true` if this network and the given network are both in
    /// the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use std::str::FromStr;
    /// use ipnet::Ipv6Net;
    ///
    /// let net1 = Ipv6Net::from_str("fd00::/18").unwrap();
    /// let net2 = Ipv6Net::from_str("fd00:4000::/18").unwrap();
    /// let net3 = Ipv6Net::from_str("fd00:8000::/18").unwrap();
    /// assert!(net1.sibling_of(&net2));
    /// assert!(!net2.sibling_of(&net3));
    /// ```
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

// TODO: How can we make all of this aggregation section more generic?
impl IpNet {
    pub fn aggregate(networks: &Vec<IpNet>) -> Vec<IpNet> {
        let mut aggs: Vec<IpNet> = Ipv4Net::aggregate(
            &networks.iter().filter_map(|p| if let IpNet::V4(x) = *p { Some(x) } else { None }).collect()
        ).into_iter().map(|n| IpNet::V4(n)).collect();

        aggs.extend::<Vec<IpNet>>(Ipv6Net::aggregate(
            &networks.iter().filter_map(|p| if let IpNet::V6(x) = *p { Some(x) } else { None }).collect()
        ).into_iter().map(|n| IpNet::V6(n)).collect());
        aggs
    }
}

impl Ipv4Net {
    // TODO: Will be interesting to experiment with Range types.
    fn interval(&self) -> (u32, u32) {
        (
            u32::from(self.network()),
            u32::from(self.broadcast()).saturating_add(1),
        )
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
    fn interval(&self) -> (Emu128, Emu128) {
        (
            Emu128::from(self.network()),
            Emu128::from(self.broadcast()).saturating_add(Emu128 { hi: 0, lo: 1 }),
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
                let range = end.saturating_sub(start);
                let num_bits = 128u32.saturating_sub(range.leading_zeros()).saturating_sub(1);
                let prefix_len = 128 - min(num_bits, start.trailing_zeros());
                //res.push(Ipv6Net::new(ipv6_addr_from_Emu128(start), prefix_len as u8));
                res.push(Ipv6Net::new(start.into(), prefix_len as u8));
                let step = if prefix_len <= 64 { Emu128 { hi: 1 << (64 - prefix_len), lo: 0 } }
                else { Emu128 { hi: 0, lo: 1 << (128 - prefix_len) } };
                start = start.saturating_add(step);
            }
        }
        res
    }
}
