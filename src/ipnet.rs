use std::cmp::{min, max};
use std::convert::From;
use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::ops::Deref;
use std::option::Option::{Some, None};

use emu128::Emu128;
use ipext::{IpAddrIter, IpAdd, IpBitAnd, IpBitOr};
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
/// use std::str::FromStr;
/// use ipnet::{IpNet, Ipv4Net, Ipv6Net};
///
/// let net_v4 = IpNet::from_str("10.1.1.0/24").unwrap();
/// let net_v6 = IpNet::from_str("fd00::/32").unwrap();
/// 
/// assert_eq!("10.1.1.0".parse(), Ok(net_v4.network()));
/// assert_eq!("fd00::".parse(), Ok(net_v6.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum IpNet {
    V4(Ipv4Net),
    V6(Ipv6Net),
}

/// An IPv4 network address.
///
/// See [`IpNet`] for a type encompassing both IPv4 and IPv6 network
/// addresses.
///
/// # Textual representation
///
/// `Ipv4Net` provides a [`FromStr`] implementation. This is represented
/// using the `FromStr` implementation for `Ipv4Addr` followed by a `/`
/// character and the prefix length in decimal. See [IETF RFC 4632] for
/// the CIDR notation.
///
/// [`IpNet`]: enum.IpAddr.html
/// [RFC 4632]: https://tools.ietf.org/html/rfc4632
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
///
/// # Examples
///
/// ```
/// use std::net::Ipv4Addr;
/// use std::str::FromStr;
/// use ipnet::Ipv4Net;
///
/// let net_v4 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
/// assert_eq!("10.1.1.0".parse(), Ok(net_v4.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Ipv4Net {
    addr: Ipv4Addr,
    prefix_len: u8,
}

/// An IPv6 network address.
///
/// See [`IpNet`] for a type encompassing both IPv4 and IPv6 network
/// addresses.
///
/// # Textual representation
///
/// `Ipv6Net` provides a [`FromStr`] implementation. This is represented
/// using the `FromStr` implementation for `Ipv6Addr` followed by a `/`
/// character and the prefix length in decimal. See [IETF RFC 4632] for
/// the CIDR notation.
///
/// [`IpNet`]: enum.IpAddr.html
/// [IETF RFC 4632]: https://tools.ietf.org/html/rfc4632
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::Ipv6Net;
///
/// let net_v6 = Ipv6Net::from_str("fd00::/32").unwrap();
/// assert_eq!("fd00::".parse(), Ok(net_v6.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Ipv6Net {
    addr: Ipv6Addr,
    prefix_len: u8,
}

// For the time being deref method calls to the IpAddr implemenations.
// We can't do this for the IpNet enum unfortunately.

impl Deref for Ipv4Net {
    type Target = Ipv4Addr;
    fn deref(&self) -> &Self::Target {
        &self.addr
    }
}

impl Deref for Ipv6Net {
    type Target = Ipv6Addr;
    fn deref(&self) -> &Self::Target {
        &self.addr
    }
}

impl IpNet {
    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.netmask(), IpAddr::from_str("255.255.240.0").unwrap());
    ///
    /// let net = IpNet::from_str("fd00::/24").unwrap();
    /// assert_eq!(net.netmask(), IpAddr::from_str("ffff:ff00::").unwrap());
    /// ```
    pub fn netmask(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.netmask()),
            IpNet::V6(ref a) => IpAddr::V6(a.netmask()),
        }
    }

    /// Returns the host mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.hostmask(), IpAddr::from_str("0.0.15.255").unwrap());
    ///
    /// let net = IpNet::from_str("fd00::/24").unwrap();
    /// assert_eq!(net.hostmask(), IpAddr::from_str("::ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap());
    /// ```
    pub fn hostmask(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.hostmask()),
            IpNet::V6(ref a) => IpAddr::V6(a.hostmask()),
        }
    }
    
    /// Returns the network address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("172.16.123.123/16").unwrap();
    /// assert_eq!(net.network(), IpAddr::from_str("172.16.0.0").unwrap());
    ///
    /// let net = IpNet::from_str("fd00:1234:5678::/24").unwrap();
    /// assert_eq!(net.network(), IpAddr::from_str("fd00:1200::").unwrap());
    /// ```
    pub fn network(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.network()),
            IpNet::V6(ref a) => IpAddr::V6(a.network()),
        }
    }    
    
    /// Returns the broadcast address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("172.16.0.0/22").unwrap();
    /// assert_eq!(net.broadcast(), IpAddr::from_str("172.16.3.255").unwrap());
    ///
    /// let net = IpNet::from_str("fd00:1234:5678::/24").unwrap();
    /// assert_eq!(net.broadcast(), IpAddr::from_str("fd00:12ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap());
    /// ```
    pub fn broadcast(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.broadcast()),
            IpNet::V6(ref a) => IpAddr::V6(a.broadcast()),
        }
    }

    /// Returns the `IpNet` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("172.16.1.0/24").unwrap();
    /// assert_eq!(net.supernet().network(), IpAddr::from_str("172.16.0.0").unwrap());
    ///
    /// let net = IpNet::from_str("fd00:ff00::/24").unwrap();
    /// assert_eq!(net.supernet().network(), IpAddr::from_str("fd00:fe00::").unwrap());
    /// ```
    pub fn supernet(&self) -> IpNet {
        match *self {
            IpNet::V4(ref a) => IpNet::V4(a.supernet()),
            IpNet::V6(ref a) => IpNet::V6(a.supernet()),
        }
    }
    
    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// If `new_prefix_len` is less than the current prefix length or
    /// greater than the bit width of the underlying IP address type it
    /// will be clamped to both respectively.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net = IpNet::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(26).collect::<Vec<IpNet>>(), vec![
    ///     IpNet::from_str("10.0.0.0/26").unwrap(),
    ///     IpNet::from_str("10.0.0.64/26").unwrap(),
    ///     IpNet::from_str("10.0.0.128/26").unwrap(),
    ///     IpNet::from_str("10.0.0.192/26").unwrap(),
    /// ]);
    ///
    /// let net = IpNet::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(18).collect::<Vec<IpNet>>(), vec![
    ///     IpNet::from_str("fd00::/18").unwrap(),
    ///     IpNet::from_str("fd00:4000::/18").unwrap(),
    ///     IpNet::from_str("fd00:8000::/18").unwrap(),
    ///     IpNet::from_str("fd00:c000::/18").unwrap(),
    /// ]);
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> IpNetIter<IpNet> {
        match *self {
            IpNet::V4(ref a) => {
                let new_prefix_len = if new_prefix_len > 32 {
                    32
                }
                else if new_prefix_len < a.prefix_len {
                    a.prefix_len
                }
                else {
                    new_prefix_len
                };
                
                IpNetIter::new(
                    IpNet::V4(Ipv4Net::new(a.network(), new_prefix_len)),
                    IpNet::V4(Ipv4Net::new(a.broadcast(), new_prefix_len)),
                )
            },
            IpNet::V6(ref a) => {
                let new_prefix_len = if new_prefix_len > 128 {
                    128
                }
                else if new_prefix_len < a.prefix_len {
                    a.prefix_len
                }
                else {
                    new_prefix_len
                };
                
                IpNetIter::new(
                    IpNet::V6(Ipv6Net::new(a.network(), new_prefix_len)),
                    IpNet::V6(Ipv6Net::new(a.broadcast(), new_prefix_len)),
                )
            },
        }
    }

    /// Returns `true` if this network and the given network are both in
    /// the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// #
    /// let net1 = IpNet::from_str("10.1.0.0/24").unwrap();
    /// let net2 = IpNet::from_str("10.1.1.0/24").unwrap();
    /// let net3 = IpNet::from_str("10.1.2.0/24").unwrap();
    /// assert!(net1.sibling_of(&net2));
    /// assert!(!net2.sibling_of(&net3));
    ///
    /// let net61 = IpNet::from_str("fd00::/18").unwrap();
    /// let net62 = IpNet::from_str("fd00:4000::/18").unwrap();
    /// let net63 = IpNet::from_str("fd00:8000::/18").unwrap();
    /// assert!(net61.sibling_of(&net62));
    /// assert!(!net62.sibling_of(&net63));
    /// assert!(!net1.sibling_of(&net62));
    /// ```
    pub fn sibling_of(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.sibling_of(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.sibling_of(b),
            (_, _) => false,
        }
    }

    // TODO: How can we make all of this aggregation section more generic?
    pub fn aggregate(networks: &Vec<IpNet>) -> Vec<IpNet> {
        // TODO: Woah this came out ugly.
        let mut aggs: Vec<IpNet> = Ipv4Net::aggregate(
            &networks.iter().filter_map(|p| if let IpNet::V4(x) = *p { Some(x) } else { None }).collect()
        ).into_iter().map(|n| IpNet::V4(n)).collect();

        aggs.extend::<Vec<IpNet>>(Ipv6Net::aggregate(
            &networks.iter().filter_map(|p| if let IpNet::V6(x) = *p { Some(x) } else { None }).collect()
        ).into_iter().map(|n| IpNet::V6(n)).collect());
        aggs
    }
}

impl fmt::Debug for IpNet {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, fmt)
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

impl From<Ipv4Net> for IpNet {
    fn from(net: Ipv4Net) -> IpNet {
        IpNet::V4(net)
    }
}

impl From<Ipv6Net> for IpNet {
    fn from(net: Ipv6Net) -> IpNet {
        IpNet::V6(net)
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

impl Ipv4Net {
    /// Creates a new IPv4 network address from an `Ipv4Addr` and prefix
    /// length.
    ///
    /// If `prefix_len` is greater than 32 it will be clamped to 32.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::new(Ipv4Addr::new(10, 1, 1, 0), 24);
    /// ```
    pub fn new(ip: Ipv4Addr, prefix_len: u8) -> Ipv4Net {
        let prefix_len = if prefix_len > 32 { 32 } else { prefix_len };
        Ipv4Net { addr: ip, prefix_len: prefix_len }
    }

    /// Returns the prefix length.
    pub fn prefix_len(&self) -> u8 {
        self.prefix_len
    }

    /// Experimental.
    pub fn truncated(&self) -> Ipv4Net {
        Ipv4Net::new(self.network(), self.prefix_len)
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.netmask(), Ipv4Addr::from_str("255.255.240.0").unwrap());
    /// ```
    pub fn netmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::max_value().saturating_shl(32 - self.prefix_len))
    }

    /// Returns the host mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.hostmask(), Ipv4Addr::from_str("0.0.15.255").unwrap());
    /// ```
    pub fn hostmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::max_value().saturating_shr(self.prefix_len))
    }

    /// Returns the network address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("172.16.123.123/16").unwrap();
    /// assert_eq!(net.network(), Ipv4Addr::from_str("172.16.0.0").unwrap());
    /// ```
    pub fn network(&self) -> Ipv4Addr {
        self.addr.bitand(u32::max_value().saturating_shl(32 - self.prefix_len))
    }

    /// Returns the broadcast address. Returns the provided Ipv4Addr
    /// with all bits after the prefix length set.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("172.16.0.0/22").unwrap();
    /// assert_eq!(net.broadcast(), Ipv4Addr::from_str("172.16.3.255").unwrap());
    /// ```
    pub fn broadcast(&self) -> Ipv4Addr {
        self.addr.bitor(u32::max_value().saturating_shr(self.prefix_len))
    }

    /// Returns the `Ipv4Net` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("172.16.1.0/24").unwrap();
    /// assert_eq!(net.supernet().network(), Ipv4Addr::from_str("172.16.0.0").unwrap());
    /// ```
    pub fn supernet(&self) -> Ipv4Net {
        Ipv4Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// If `new_prefix_len` is less than the current prefix length or
    /// greater than 32 it will be clamped to both respectively.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net = Ipv4Net::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(26).collect::<Vec<Ipv4Net>>(), vec![
    ///     Ipv4Net::from_str("10.0.0.0/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.64/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.128/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.192/26").unwrap(),
    /// ]);
    ///
    /// let net = Ipv4Net::from_str("10.0.0.0/30").unwrap();
    /// assert_eq!(net.subnets(32).collect::<Vec<Ipv4Net>>(), vec![
    ///     Ipv4Net::from_str("10.0.0.0/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.1/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.2/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.3/32").unwrap(),
    /// ]);
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> IpNetIter<Ipv4Net> {
        let new_prefix_len = if new_prefix_len > 32 {
            32
        }
        else if new_prefix_len < self.prefix_len {
            self.prefix_len
        }
        else {
            new_prefix_len
        };

        IpNetIter::new(
            Ipv4Net::new(self.network(), new_prefix_len),
            Ipv4Net::new(self.broadcast(), new_prefix_len),
        )
    }
    
    /// Return an `Iterator` over the host addresses in this network.
    pub fn hosts(&self) -> IpAddrIter<Ipv4Addr> {
        IpAddrIter::new(
            self.network(),
            self.broadcast(),
        )
    }
    
    /// Returns `true` if this network and the given network are both in
    /// the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// #
    /// let net1 = Ipv4Net::from_str("10.1.0.0/24").unwrap();
    /// let net2 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
    /// let net3 = Ipv4Net::from_str("10.1.2.0/24").unwrap();
    /// assert!(net1.sibling_of(&net2));
    /// assert!(!net2.sibling_of(&net3));
    /// ```
    pub fn sibling_of(&self, other: &Ipv4Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }

    // TODO: Will be interesting to experiment with Range types.
    fn interval(&self) -> (u32, u32) {
        (
            u32::from(self.network()),
            u32::from(self.broadcast()).saturating_add(1),
        )
    }

    /// Experimental.
    pub fn aggregate(networks: &Vec<Ipv4Net>) -> Vec<Ipv4Net> {
        // TODO: Should this return an iterator instead?
        let mut intervals: Vec<(_, _)> = networks.iter().map(|n| n.interval()).collect();
        
        intervals = merge_intervals(intervals);
        let mut res: Vec<Ipv4Net> = Vec::new();

        // Break up merged intervals into the largest subnets that will fit.
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

impl fmt::Debug for Ipv4Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, fmt)
    }
}

impl fmt::Display for Ipv4Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.addr, self.prefix_len)
    }
}

impl Ipv6Net {    
    /// Creates a new IPv4 network address from an `Ipv4Addr` and prefix
    /// length.
    ///
    /// If `prefix_len` is greater than 128 it will be clamped to 128.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
    /// let net = Ipv6Net::new(Ipv6Addr::from_str("fd00::").unwrap(), 24);
    /// ```
    pub fn new(ip: Ipv6Addr, prefix_len: u8) -> Ipv6Net {
        let prefix_len = if prefix_len > 128 { 128 } else { prefix_len };
        Ipv6Net { addr: ip, prefix_len: prefix_len }
    }

    /// Returns the prefix length.
    pub fn prefix_len(&self) -> u8 {
        self.prefix_len
    }

    /// Experimental.
    pub fn truncated(&self) -> Ipv6Net {
        Ipv6Net::new(self.network(), self.prefix_len)
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
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
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
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
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
    /// let net = Ipv6Net::from_str("fd00:1234:5678::/24").unwrap();
    /// assert_eq!(net.network(), Ipv6Addr::from_str("fd00:1200::").unwrap());
    /// ```
    pub fn network(&self) -> Ipv6Addr {
        self.addr.bitand(Emu128::max_value().saturating_shl(128 - self.prefix_len))
    }
    
    /// Returns the broadcast address. Returns the provided Ipv6Addr
    /// with all bits after the prefix length set.
    ///
    /// * Technically there is no such thing as a broadcast address in
    ///   in IPv6. Perhaps we should change the methods to first() and
    ///   last() or start() and end().
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
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
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
    /// let net = Ipv6Net::from_str("fd00:ff00::/24").unwrap();
    /// assert_eq!(net.supernet().network(), Ipv6Addr::from_str("fd00:fe00::").unwrap());
    /// ```
    pub fn supernet(&self) -> Ipv6Net {
        Ipv6Net::new(self.addr.clone(), self.prefix_len - 1)
    }

    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// If `new_prefix_len` is less than the current prefix length or
    /// greater than 128 it will be clamped to both respectively.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// let net = Ipv6Net::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(18).collect::<Vec<Ipv6Net>>(), vec![
    ///     Ipv6Net::from_str("fd00::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:4000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:8000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:c000::/18").unwrap(),
    /// ]);
    ///
    /// let net = Ipv6Net::from_str("fd00::/126").unwrap();
    /// assert_eq!(net.subnets(128).collect::<Vec<Ipv6Net>>(), vec![
    ///     Ipv6Net::from_str("fd00::/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::1/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::2/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::3/128").unwrap(),
    /// ]);
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> IpNetIter<Ipv6Net> {
        let new_prefix_len = if new_prefix_len > 128 {
            128
        }
        else if new_prefix_len < self.prefix_len {
            self.prefix_len
        }
        else {
            new_prefix_len
        };
        
        IpNetIter::new(
            Ipv6Net::new(self.network(), new_prefix_len),
            Ipv6Net::new(self.broadcast(), new_prefix_len),
        )
    }

    /// Return an `Iterator` over the host addresses in this network.
    pub fn hosts(&self) -> IpAddrIter<Ipv6Addr> {
        IpAddrIter::new(
            self.network(),
            self.broadcast(),
        )
    }

    /// Returns `true` if this network and the given network are both in
    /// the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// #
    /// let net1 = Ipv6Net::from_str("fd00::/18").unwrap();
    /// let net2 = Ipv6Net::from_str("fd00:4000::/18").unwrap();
    /// let net3 = Ipv6Net::from_str("fd00:8000::/18").unwrap();
    /// assert!(net1.sibling_of(&net2));
    /// assert!(!net2.sibling_of(&net3));
    /// ```
    pub fn sibling_of(&self, other: &Ipv6Net) -> bool {
        self.prefix_len == other.prefix_len && self.supernet().contains(other)
    }

    // TODO: Will be interesting to experiment with Range types.
    fn interval(&self) -> (Emu128, Emu128) {
        (
            Emu128::from(self.network()),
            Emu128::from(self.broadcast()).saturating_add(Emu128 { hi: 0, lo: 1 }),
        )
    }

    /// Experimental.
    pub fn aggregate(networks: &Vec<Ipv6Net>) -> Vec<Ipv6Net> {
        // TODO: Should this return an iterator instead?
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

impl fmt::Debug for Ipv6Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, fmt)
    }
}

impl fmt::Display for Ipv6Net {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.addr, self.prefix_len)
    }
}

/// Provides a `contains()` method to test if a network contains another network or
/// address.
pub trait Contains<T> {
    /// Returns `true` if this network contains the given network or
    /// address.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::IpAddr;
    /// use std::str::FromStr;
    /// use ipnet::{IpNet, Contains};
    /// ```
    ///
    /// `Ipv4Net` can contain `Ipv4Net` and `Ipv4Addr`.
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::{IpNet, Contains};
    /// let n1 = IpNet::from_str("10.1.1.0/24").unwrap();
    /// let n2 = IpNet::from_str("10.1.1.0/26").unwrap();
    /// let n3 = IpNet::from_str("10.1.2.0/26").unwrap();
    /// let ip1 = IpAddr::from_str("10.1.1.1").unwrap();
    /// let ip2 = IpAddr::from_str("10.1.2.1").unwrap();
    /// assert!(n1.contains(&n2));
    /// assert!(n1.contains(&ip1));
    /// assert!(!n1.contains(&n3));
    /// assert!(!n1.contains(&ip2));
    /// ```
    ///
    /// `Ipv6Net` can contain `Ipv6Net` and `Ipv6Addr`.
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::{IpNet, Contains};
    /// let n6_1 = IpNet::from_str("fd00::/16").unwrap();
    /// let n6_2 = IpNet::from_str("fd00::/17").unwrap();
    /// let n6_3 = IpNet::from_str("fd01::/17").unwrap();
    /// let ip6_1 = IpAddr::from_str("fd00::1").unwrap();
    /// let ip6_2 = IpAddr::from_str("fd01::1").unwrap();
    /// assert!(n6_1.contains(&n6_2));
    /// assert!(n6_1.contains(&ip6_1));
    /// assert!(!n6_1.contains(&n6_3));
    /// assert!(!n6_1.contains(&ip6_2));
    /// ```
    ///
    /// `Ipv4Net` and `Ipv6Net` types cannot contain each other.
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::{IpNet, Contains};
    /// # let n1 = IpNet::from_str("10.1.1.0/24").unwrap();
    /// # let ip1 = IpAddr::from_str("10.1.1.1").unwrap();
    /// # let n6_1 = IpNet::from_str("fd00::/16").unwrap();
    /// # let ip6_1 = IpAddr::from_str("fd00::1").unwrap();
    /// assert!(!n1.contains(&n6_1) && !n6_1.contains(&n1));
    /// assert!(!n1.contains(&ip6_1) && !n6_1.contains(&ip1));
    /// ```
    fn contains(&self, other: T) -> bool;
}

impl<'a> Contains<&'a IpNet> for IpNet {
    fn contains(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.contains(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.contains(b),
            _ => false,
        }
    }
}

impl<'a> Contains<&'a IpAddr> for IpNet {
    fn contains(&self, other: &IpAddr) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpAddr::V4(ref b)) => a.contains(b),
            (IpNet::V6(ref a), IpAddr::V6(ref b)) => a.contains(b),
            _ => false,
        }
    }
}

impl<'a> Contains<&'a Ipv4Net> for Ipv4Net {
    fn contains(&self, other: &'a Ipv4Net) -> bool {
        self.network() <= other.network() && other.broadcast() <= self.broadcast()
    }
}

impl<'a> Contains<&'a Ipv4Addr> for Ipv4Net {
    fn contains(&self, other: &'a Ipv4Addr) -> bool {
        self.network() <= *other && *other <= self.broadcast()
    }
}

impl<'a> Contains<&'a Ipv6Net> for Ipv6Net {
    fn contains(&self, other: &'a Ipv6Net) -> bool {
        self.network() <= other.network() && other.broadcast() <= self.broadcast()
    }
}

impl<'a> Contains<&'a Ipv6Addr> for Ipv6Net {
    fn contains(&self, other: &'a Ipv6Addr) -> bool {
        self.network() <= *other && *other <= self.broadcast()
    }
}

/// An `Iterator` over a range of IP network addresses.
///
/// This might be deprecated and replaced with an implementation of
/// `Range` when it and its required traits are stablized.
///
/// # Examples
///
/// ```
/// use std::str::FromStr;
/// use ipnet::{IpNet, Ipv4Net, Ipv6Net, IpNetIter};
///
/// let i = IpNetIter::new(IpNet::from_str("10.0.0.0/26").unwrap(), IpNet::from_str("10.0.0.192/26").unwrap());
/// let i4 = IpNetIter::new(Ipv4Net::from_str("10.0.0.0/26").unwrap(), Ipv4Net::from_str("10.0.0.192/26").unwrap());
/// let i6 = IpNetIter::new(Ipv6Net::from_str("fd00::/18").unwrap(), Ipv6Net::from_str("fd00:c000::/18").unwrap());
/// 
/// assert_eq!(i.collect::<Vec<IpNet>>(), vec![
///     IpNet::from_str("10.0.0.0/26").unwrap(),
///     IpNet::from_str("10.0.0.64/26").unwrap(),
///     IpNet::from_str("10.0.0.128/26").unwrap(),
///     IpNet::from_str("10.0.0.192/26").unwrap(),
/// ]);
///
/// assert_eq!(i4.collect::<Vec<Ipv4Net>>(), vec![
///     Ipv4Net::from_str("10.0.0.0/26").unwrap(),
///     Ipv4Net::from_str("10.0.0.64/26").unwrap(),
///     Ipv4Net::from_str("10.0.0.128/26").unwrap(),
///     Ipv4Net::from_str("10.0.0.192/26").unwrap(),
/// ]);
///
/// assert_eq!(i6.collect::<Vec<Ipv6Net>>(), vec![
///     Ipv6Net::from_str("fd00::/18").unwrap(),
///     Ipv6Net::from_str("fd00:4000::/18").unwrap(),
///     Ipv6Net::from_str("fd00:8000::/18").unwrap(),
///     Ipv6Net::from_str("fd00:c000::/18").unwrap(),
/// ]);
/// ```
#[derive(Debug)]
pub struct IpNetIter<T> {
    pub start: T,
    pub end: T,
}

impl<T> IpNetIter<T> {
    pub fn new(start: T, end: T) -> Self {
        IpNetIter {
            start: start,
            end: end,
        }
    }
}

impl IpNetIter<IpNet> {
    fn forward(&self) -> IpNet {
        match self.start {
            IpNet::V4(ref a) => IpNet::V4(
                Ipv4Net::new(a.broadcast().saturating_add(1), a.prefix_len)
            ),
            IpNet::V6(ref a) => IpNet::V6(
                Ipv6Net::new(a.broadcast().saturating_add(1), a.prefix_len)
            ),
        }
    }
}

impl IpNetIter<Ipv4Net> {
    fn forward(&self) -> Ipv4Net {
        Ipv4Net::new(self.start.broadcast().saturating_add(1), self.start.prefix_len)
    }
}

impl IpNetIter<Ipv6Net> {
    fn forward(&self) -> Ipv6Net {
        Ipv6Net::new(self.start.broadcast().saturating_add(1), self.start.prefix_len)
    }
}

// TODO: Will infinitely loop if end is all ones because start <= end.
impl Iterator for IpNetIter<IpNet> {
    type Item = IpNet;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.start <= self.end {
            let res = Some(self.start);
            self.start = self.forward();
            return res;
        }
        None
    }
}

impl Iterator for IpNetIter<Ipv4Net> {
    type Item = Ipv4Net;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.start <= self.end {
            let res = Some(self.start);
            self.start = self.forward();
            return res;
        }
        None
    }
}

impl Iterator for IpNetIter<Ipv6Net> {
    type Item = Ipv6Net;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.start <= self.end {
            let res = Some(self.start);
            self.start = self.forward();
            return res;
        }
        None
    }
}
