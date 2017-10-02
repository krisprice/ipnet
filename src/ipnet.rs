use std::cmp::{min, max};
use std::cmp::Ordering::{Less, Equal};
use std::convert::From;
use std::error::Error;
use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::ops::Deref;
use std::option::Option::{Some, None};

use emu128::Emu128;
use ipext::{IpAdd, IpSub, IpStep, IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};

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
///
/// let net_v4 = "10.1.1.0/24".parse::<Ipv4Net>().unwrap();
/// let net_v6 = "fd00::/32".parse::<Ipv6Net>().unwrap();
///
/// assert_eq!("10.1.1.0".parse(), Ok(net_v4.network()));
/// assert_eq!("fd00::".parse(), Ok(net_v6.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
/// `Ipv4Net` provides a [`FromStr`] implementation for parsing networks
/// represented in CIDR notation. This uses the same representation as
/// [`Ipv4Addr`] followed by the `/` character and the prefix length in
/// decimal. See [IETF RFC 4632] for the CIDR notation.
///
/// [`IpNet`]: enum.IpAddr.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Ipv4Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv4Addr.html
/// [IETF RFC 4632]: https://tools.ietf.org/html/rfc4632
///
/// # Examples
///
/// ```
/// use std::net::Ipv4Addr;
/// use ipnet::Ipv4Net;
///
/// let net_v4 = "10.1.1.0/24".parse::<Ipv4Net>().unwrap();
/// assert_eq!("10.1.1.0".parse(), Ok(net_v4.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
/// `Ipv6Net` provides a [`FromStr`] implementation for parsing networks
/// represented in CIDR notation. This uses the same representation as
/// [`Ipv6Addr`] followed by the `/` character and the prefix length in
/// decimal. See [IETF RFC 4632] for the CIDR notation.
///
/// [`IpNet`]: enum.IpAddr.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Ipv6Addr`]: https://doc.rust-lang.org/std/net/struct.Ipv6Addr.html
/// [IETF RFC 4632]: https://tools.ietf.org/html/rfc4632
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use ipnet::Ipv6Net;
///
/// let net_v6 = "fd00::/32".parse::<Ipv6Net>().unwrap();
/// assert_eq!("fd00::".parse(), Ok(net_v6.network()));
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Ipv6Net {
    addr: Ipv6Addr,
    prefix_len: u8,
}

/// An error that is returned when the prefix length is invalid. Valid
/// prefix lengths are 0 to 32 for IPv4 and 0 to 128 for IPv6.
///
/// This error is used as the error type for the `new()` and `subnets()`
/// methods on [`Ipv4Net`] and [`Ipv6Net`].
///
/// [`Ipv4Net`]: struct.Ipv4Net.html
/// [`Ipv6Net`]: struct.Ipv6Net.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrefixLenError;

impl fmt::Display for PrefixLenError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(self.description())
    }
}

impl Error for PrefixLenError {
    fn description(&self) -> &str {
        "invalid IP prefix length"
    }
}

// For the time being deref method calls to the Ipv4Addr and Ipv6Addr
// implemenations. We can't do this for the IpNet enum unfortunately.
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
    /// Returns a copy of the network with the address truncated to the
    /// prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// assert_eq!(
    ///     IpNet::from_str("192.168.12.34/16").unwrap().trunc(),
    ///     IpNet::from_str("192.168.0.0/16").unwrap()
    /// );
    ///
    /// assert_eq!(
    ///     IpNet::from_str("fd00::1:2:3:4/16").unwrap().trunc(),
    ///     IpNet::from_str("fd00::/16").unwrap()
    /// );
    /// ```
    pub fn trunc(&self) -> IpNet {
        match *self {
            IpNet::V4(ref a) => IpNet::V4(a.trunc()),
            IpNet::V6(ref a) => IpNet::V6(a.trunc()),
        }
    }

    /// Returns the address.
    pub fn addr(&self) -> IpAddr {
        match *self {
            IpNet::V4(ref a) => IpAddr::V4(a.addr),
            IpNet::V6(ref a) => IpAddr::V6(a.addr),
        }
    }

    /// Returns the prefix length.
    pub fn prefix_len(&self) -> u8 {
        match *self {
            IpNet::V4(ref a) => a.prefix_len(),
            IpNet::V6(ref a) => a.prefix_len(),
        }
    }

    /// Returns the maximum valid prefix length.
    pub fn max_prefix_len(&self) -> u8 {
        match *self {
            IpNet::V4(ref a) => a.max_prefix_len(),
            IpNet::V6(ref a) => a.max_prefix_len(),
        }
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
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
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// let n1 = IpNet::from_str("172.16.1.0/24").unwrap();
    /// let n2 = IpNet::from_str("172.16.0.0/23").unwrap();
    /// let n3 = IpNet::from_str("172.16.0.0/0").unwrap();
    ///
    /// assert_eq!(n1.supernet().unwrap(), n2);
    /// assert_eq!(n3.supernet(), None);
    ///
    /// let n1 = IpNet::from_str("fd00:ff00::/24").unwrap();
    /// let n2 = IpNet::from_str("fd00:fe00::/23").unwrap();
    /// let n3 = IpNet::from_str("fd00:fe00::/0").unwrap();
    ///
    /// assert_eq!(n1.supernet().unwrap(), n2);
    /// assert_eq!(n3.supernet(), None);
    /// ```
    pub fn supernet(&self) -> Option<IpNet> {
        match *self {
            IpNet::V4(ref a) => a.supernet().map(IpNet::V4),
            IpNet::V6(ref a) => a.supernet().map(IpNet::V6),
        }
    }

    /// Returns `true` if this network and the given network are 
    /// children of the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// let net4_1 = IpNet::from_str("10.1.0.0/24").unwrap();
    /// let net4_2 = IpNet::from_str("10.1.1.0/24").unwrap();
    /// let net4_3 = IpNet::from_str("10.1.2.0/24").unwrap();
    /// let net6_1 = IpNet::from_str("fd00::/18").unwrap();
    /// let net6_2 = IpNet::from_str("fd00:4000::/18").unwrap();
    /// let net6_3 = IpNet::from_str("fd00:8000::/18").unwrap();
    ///
    /// assert!( net4_1.is_sibling(&net4_2));
    /// assert!(!net4_2.is_sibling(&net4_3));
    /// assert!( net6_1.is_sibling(&net6_2));
    /// assert!(!net6_2.is_sibling(&net6_3));
    /// assert!(!net4_1.is_sibling(&net6_2));
    /// ```
    pub fn is_sibling(&self, other: &IpNet) -> bool {
        match (*self, *other) {
            (IpNet::V4(ref a), IpNet::V4(ref b)) => a.is_sibling(b),
            (IpNet::V6(ref a), IpNet::V6(ref b)) => a.is_sibling(b),
            _ => false,
        }
    }

    /// Return an `Iterator` over the host addresses in this network.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::IpAddr;
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// let net = IpNet::from_str("10.0.0.0/30").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<IpAddr>>(), vec![
    ///     IpAddr::from_str("10.0.0.1").unwrap(),
    ///     IpAddr::from_str("10.0.0.2").unwrap(),
    /// ]);
    ///
    /// let net = IpNet::from_str("10.0.0.0/31").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<IpAddr>>(), vec![
    ///     IpAddr::from_str("10.0.0.0").unwrap(),
    ///     IpAddr::from_str("10.0.0.1").unwrap(),
    /// ]);
    ///
    /// let net = IpNet::from_str("fd00::/126").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<IpAddr>>(), vec![
    ///     IpAddr::from_str("fd00::").unwrap(),
    ///     IpAddr::from_str("fd00::1").unwrap(),
    ///     IpAddr::from_str("fd00::2").unwrap(),
    ///     IpAddr::from_str("fd00::3").unwrap(),
    /// ]);
    /// ```
    pub fn hosts(&self) -> IpAddrRange {
        match *self {
            IpNet::V4(ref a) => IpAddrRange::V4(a.hosts()),
            IpNet::V6(ref a) => IpAddrRange::V6(a.hosts()),
        }
    }
    
    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::{IpNet, PrefixLenError};
    /// let net = IpNet::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(26).unwrap().collect::<Vec<IpNet>>(), vec![
    ///     IpNet::from_str("10.0.0.0/26").unwrap(),
    ///     IpNet::from_str("10.0.0.64/26").unwrap(),
    ///     IpNet::from_str("10.0.0.128/26").unwrap(),
    ///     IpNet::from_str("10.0.0.192/26").unwrap(),
    /// ]);
    ///
    /// let net = IpNet::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(18).unwrap().collect::<Vec<IpNet>>(), vec![
    ///     IpNet::from_str("fd00::/18").unwrap(),
    ///     IpNet::from_str("fd00:4000::/18").unwrap(),
    ///     IpNet::from_str("fd00:8000::/18").unwrap(),
    ///     IpNet::from_str("fd00:c000::/18").unwrap(),
    /// ]);
    ///
    /// let net = IpNet::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(23), Err(PrefixLenError));
    ///
    /// let net = IpNet::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(33), Err(PrefixLenError));
    ///
    /// let net = IpNet::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(15), Err(PrefixLenError));
    ///
    /// let net = IpNet::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(129), Err(PrefixLenError));
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> Result<Subnets<IpAddr>, PrefixLenError> {
        if self.prefix_len() > new_prefix_len || new_prefix_len > self.max_prefix_len() {
            return Err(PrefixLenError);
        }

        Ok(Subnets::new(
            self.network(),
            self.broadcast(),
            new_prefix_len,
        ))
    }

    /// Aggregate a `Vec` of `IpNet`s and return the result as a new
    /// `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::IpNet;
    /// let ipnets = vec![
    ///     IpNet::from_str("10.0.0.0/24").unwrap(),
    ///     IpNet::from_str("10.0.1.0/24").unwrap(),
    ///     IpNet::from_str("10.0.2.0/24").unwrap(),
    ///     IpNet::from_str("fd00::/18").unwrap(),
    ///     IpNet::from_str("fd00:4000::/18").unwrap(),
    ///     IpNet::from_str("fd00:8000::/18").unwrap(),
    /// ];
    /// assert_eq!(IpNet::aggregate(&ipnets), vec![
    ///     IpNet::from_str("10.0.0.0/23").unwrap(),
    ///     IpNet::from_str("10.0.2.0/24").unwrap(),
    ///     IpNet::from_str("fd00::/17").unwrap(),
    ///     IpNet::from_str("fd00:8000::/18").unwrap(),
    /// ]);
    /// ```
    pub fn aggregate(networks: &Vec<IpNet>) -> Vec<IpNet> {
        // It's 2.5x faster to split the input up and run them using the
        // specific IPv4 and IPV6 implementations. The comparisons and
        // merge_intervals are much faster running over integers.
        let mut ipv4nets: Vec<Ipv4Net> = Vec::new();
        let mut ipv6nets: Vec<Ipv6Net> = Vec::new();

        for n in networks {
            match *n {
                IpNet::V4(x) => ipv4nets.push(x),
                IpNet::V6(x) => ipv6nets.push(x),
            }
        }

        let mut res: Vec<IpNet> = Vec::new();
        let ipv4aggs = Ipv4Net::aggregate(&ipv4nets);
        let ipv6aggs = Ipv6Net::aggregate(&ipv6nets);
        res.extend::<Vec<IpNet>>(ipv4aggs.into_iter().map(IpNet::V4).collect::<Vec<IpNet>>());
        res.extend::<Vec<IpNet>>(ipv6aggs.into_iter().map(IpNet::V6).collect::<Vec<IpNet>>());
        res
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

impl Ipv4Net {
    /// Creates a new IPv4 network address from an `Ipv4Addr` and prefix
    /// length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    /// use ipnet::{Ipv4Net, PrefixLenError};
    ///
    /// let net = Ipv4Net::new(Ipv4Addr::new(10, 1, 1, 0), 24);
    /// assert!(net.is_ok());
    ///
    /// let bad_prefix_len = Ipv4Net::new(Ipv4Addr::new(10, 1, 1, 0), 33);
    /// assert_eq!(bad_prefix_len, Err(PrefixLenError));
    /// ```
    pub fn new(ip: Ipv4Addr, prefix_len: u8) -> Result<Ipv4Net, PrefixLenError> {
        if prefix_len > 32 {
            return Err(PrefixLenError);
        }
        Ok(Ipv4Net { addr: ip, prefix_len: prefix_len })
    }

    /// Returns a copy of the network with the address truncated to the
    /// prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// assert_eq!(
    ///     Ipv4Net::from_str("192.168.12.34/16").unwrap().trunc(),
    ///     Ipv4Net::from_str("192.168.0.0/16").unwrap()
    /// );
    /// ```
    pub fn trunc(&self) -> Ipv4Net {
        Ipv4Net::new(self.network(), self.prefix_len).unwrap()
    }

    /// Returns the address.
    pub fn addr(&self) -> Ipv4Addr {
        self.addr
    }

    /// Returns the prefix length.
    pub fn prefix_len(&self) -> u8 {
        self.prefix_len
    }

    /// Returns the maximum valid prefix length.
    pub fn max_prefix_len(&self) -> u8 {
        32
    }
    
    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.netmask(), Ipv4Addr::from_str("255.255.240.0").unwrap());
    /// ```
    pub fn netmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(self.netmask_u32())
    }

    fn netmask_u32(&self) -> u32 {
        u32::max_value().checked_shl(32 - self.prefix_len as u32).unwrap_or(0)
    }

    /// Returns the host mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net = Ipv4Net::from_str("10.1.0.0/20").unwrap();
    /// assert_eq!(net.hostmask(), Ipv4Addr::from_str("0.0.15.255").unwrap());
    /// ```
    pub fn hostmask(&self) -> Ipv4Addr {
        Ipv4Addr::from(self.hostmask_u32())
    }

    fn hostmask_u32(&self) -> u32 {
        u32::max_value().checked_shr(self.prefix_len as u32).unwrap_or(0)
    }

    /// Returns the network address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net = Ipv4Net::from_str("172.16.123.123/16").unwrap();
    /// assert_eq!(net.network(), Ipv4Addr::from_str("172.16.0.0").unwrap());
    /// ```
    pub fn network(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::from(self.addr) & self.netmask_u32())
    }

    /// Returns the broadcast address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net = Ipv4Net::from_str("172.16.0.0/22").unwrap();
    /// assert_eq!(net.broadcast(), Ipv4Addr::from_str("172.16.3.255").unwrap());
    /// ```
    pub fn broadcast(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::from(self.addr) | self.hostmask_u32())
    }

    /// Returns the `Ipv4Net` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let n1 = Ipv4Net::from_str("172.16.1.0/24").unwrap();
    /// let n2 = Ipv4Net::from_str("172.16.0.0/23").unwrap();
    /// let n3 = Ipv4Net::from_str("172.16.0.0/0").unwrap();
    ///
    /// assert_eq!(n1.supernet().unwrap(), n2);
    /// assert_eq!(n3.supernet(), None);
    /// ```
    pub fn supernet(&self) -> Option<Ipv4Net> {
        Ipv4Net::new(self.addr, self.prefix_len.wrapping_sub(1)).map(|n| n.trunc()).ok()
    }

    /// Returns `true` if this network and the given network are 
    /// children of the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net1 = Ipv4Net::from_str("10.1.0.0/24").unwrap();
    /// let net2 = Ipv4Net::from_str("10.1.1.0/24").unwrap();
    /// let net3 = Ipv4Net::from_str("10.1.2.0/24").unwrap();
    /// assert!(net1.is_sibling(&net2));
    /// assert!(!net2.is_sibling(&net3));
    /// ```
    pub fn is_sibling(&self, other: &Ipv4Net) -> bool {
        self.prefix_len > 0 &&
        self.prefix_len == other.prefix_len &&
        self.supernet().unwrap().contains(other)
    }
    
    /// Return an `Iterator` over the host addresses in this network.
    ///
    /// If the prefix length is less than 31 both the network address
    /// and broadcast address are excluded. These are only valid host
    /// addresses when the prefix length is 31.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv4Net;
    /// let net = Ipv4Net::from_str("10.0.0.0/30").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<Ipv4Addr>>(), vec![
    ///     Ipv4Addr::from_str("10.0.0.1").unwrap(),
    ///     Ipv4Addr::from_str("10.0.0.2").unwrap(),
    /// ]);
    ///
    /// let net = Ipv4Net::from_str("10.0.0.0/31").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<Ipv4Addr>>(), vec![
    ///     Ipv4Addr::from_str("10.0.0.0").unwrap(),
    ///     Ipv4Addr::from_str("10.0.0.1").unwrap(),
    /// ]);
    /// ```
    pub fn hosts(&self) -> Ipv4AddrRange {
        let mut start = self.network();
        let mut end = self.broadcast();
        
        if self.prefix_len < 31 {
            start = start.saturating_add(1);
            end = end.saturating_sub(1);
        }
        
        Ipv4AddrRange::new(start, end)
    }

    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::{Ipv4Net, PrefixLenError};
    /// let net = Ipv4Net::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(26).unwrap().collect::<Vec<Ipv4Net>>(), vec![
    ///     Ipv4Net::from_str("10.0.0.0/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.64/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.128/26").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.192/26").unwrap(),
    /// ]);
    ///
    /// let net = Ipv4Net::from_str("10.0.0.0/30").unwrap();
    /// assert_eq!(net.subnets(32).unwrap().collect::<Vec<Ipv4Net>>(), vec![
    ///     Ipv4Net::from_str("10.0.0.0/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.1/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.2/32").unwrap(),
    ///     Ipv4Net::from_str("10.0.0.3/32").unwrap(),
    /// ]);
    ///
    /// let net = Ipv4Net::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(23), Err(PrefixLenError));
    ///
    /// let net = Ipv4Net::from_str("10.0.0.0/24").unwrap();
    /// assert_eq!(net.subnets(33), Err(PrefixLenError));
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> Result<Subnets<Ipv4Addr>, PrefixLenError> {
        if self.prefix_len > new_prefix_len || new_prefix_len > 32 {
            return Err(PrefixLenError);
        }
        
        Ok(Subnets::new(
            self.network(),
            self.broadcast(),
            new_prefix_len,
        ))
    }

    // It is significantly faster to work on u32 than Ipv4Addr.
    fn interval(&self) -> (u32, u32) {
        (
            u32::from(self.network()),
            u32::from(self.broadcast()).saturating_add(1),
        )
    }

    /// Aggregate a `Vec` of `Ipv4Net`s and return the result as a new
    /// `Vec`.
    pub fn aggregate(networks: &Vec<Ipv4Net>) -> Vec<Ipv4Net> {
        let mut intervals: Vec<(_, _)> = networks.iter().map(|n| n.interval()).collect();
        intervals = merge_intervals(intervals);
        let mut res: Vec<Ipv4Net> = Vec::new();
        
        for (start, end) in intervals {
            let iter = Subnets::new(Ipv4Addr::from(start), Ipv4Addr::from(end.saturating_sub(1)), 0);

            for n in iter {
                res.push(n);
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
    /// Creates a new IPv6 network address from an `Ipv6Addr` and prefix
    /// length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    /// use ipnet::{Ipv6Net, PrefixLenError};
    ///
    /// let net = Ipv6Net::new(Ipv6Addr::new(0xfd, 0, 0, 0, 0, 0, 0, 0), 24);
    /// assert!(net.is_ok());
    ///
    /// let bad_prefix_len = Ipv6Net::new(Ipv6Addr::new(0xfd, 0, 0, 0, 0, 0, 0, 0), 129);
    /// assert_eq!(bad_prefix_len, Err(PrefixLenError));
    /// ```
    pub fn new(ip: Ipv6Addr, prefix_len: u8) -> Result<Ipv6Net, PrefixLenError> {
        if prefix_len > 128 {
            return Err(PrefixLenError);
        }
        Ok(Ipv6Net { addr: ip, prefix_len: prefix_len })
    }

    /// Returns a copy of the network with the address truncated to the
    /// prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// assert_eq!(
    ///     Ipv6Net::from_str("fd00::1:2:3:4/16").unwrap().trunc(),
    ///     Ipv6Net::from_str("fd00::/16").unwrap()
    /// );
    /// ```
    pub fn trunc(&self) -> Ipv6Net {
        Ipv6Net::new(self.network(), self.prefix_len).unwrap()
    }
    
    /// Returns the address.
    pub fn addr(&self) -> Ipv6Addr {
        self.addr
    }

    /// Returns the prefix length.
    pub fn prefix_len(&self) -> u8 {
        self.prefix_len
    }
    
    /// Returns the maximum valid prefix length.
    pub fn max_prefix_len(&self) -> u8 {
        128
    }

    /// Returns the network mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// assert_eq!(
    ///     Ipv6Net::from_str("fd00::/24").unwrap().netmask(),
    ///     Ipv6Addr::from_str("ffff:ff00::").unwrap()
    /// );
    /// ```
    pub fn netmask(&self) -> Ipv6Addr {
        self.netmask_emu128().into()
    }

    fn netmask_emu128(&self) -> Emu128 {
        Emu128::max_value().checked_shl(128 - self.prefix_len).unwrap_or(Emu128::min_value())
    }

    /// Returns the host mask.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// assert_eq!(
    ///     Ipv6Net::from_str("fd00::/24").unwrap().hostmask(),
    ///     Ipv6Addr::from_str("::ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap()
    /// );
    /// ```
    pub fn hostmask(&self) -> Ipv6Addr {
        self.hostmask_emu128().into()
    }

    fn hostmask_emu128(&self) -> Emu128 {
        Emu128::max_value().checked_shr(self.prefix_len).unwrap_or(Emu128::min_value())
    }

    /// Returns the network address.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// assert_eq!(
    ///     Ipv6Net::from_str("fd00:1234:5678::/24").unwrap().network(),
    ///     Ipv6Addr::from_str("fd00:1200::").unwrap()
    /// );
    /// ```
    pub fn network(&self) -> Ipv6Addr {
        (Emu128::from(self.addr) & self.netmask_emu128()).into()
    }
    
    /// Returns the last address.
    ///
    /// Technically there is no such thing as a broadcast address for
    /// IPv6. The name is used for consistency with colloquial usage.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// assert_eq!(
    ///     Ipv6Net::from_str("fd00:1234:5678::/24").unwrap().broadcast(),
    ///     Ipv6Addr::from_str("fd00:12ff:ffff:ffff:ffff:ffff:ffff:ffff").unwrap()
    /// );
    /// ```
    pub fn broadcast(&self) -> Ipv6Addr {
        (Emu128::from(self.addr) | self.hostmask_emu128()).into()
    }

    /// Returns the `Ipv6Net` that contains this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// let n1 = Ipv6Net::from_str("fd00:ff00::/24").unwrap();
    /// let n2 = Ipv6Net::from_str("fd00:fe00::/23").unwrap();
    /// let n3 = Ipv6Net::from_str("fd00:fe00::/0").unwrap();
    ///
    /// assert_eq!(n1.supernet().unwrap(), n2);
    /// assert_eq!(n3.supernet(), None);
    /// ```
    pub fn supernet(&self) -> Option<Ipv6Net> {
        Ipv6Net::new(self.addr, self.prefix_len.wrapping_sub(1)).map(|n| n.trunc()).ok()
    }

    /// Returns `true` if this network and the given network are 
    /// children of the same supernet.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// let net1 = Ipv6Net::from_str("fd00::/18").unwrap();
    /// let net2 = Ipv6Net::from_str("fd00:4000::/18").unwrap();
    /// let net3 = Ipv6Net::from_str("fd00:8000::/18").unwrap();
    /// assert!(net1.is_sibling(&net2));
    /// assert!(!net2.is_sibling(&net3));
    /// ```
    pub fn is_sibling(&self, other: &Ipv6Net) -> bool {
        self.prefix_len > 0 &&
        self.prefix_len == other.prefix_len &&
        self.supernet().unwrap().contains(other)
    }
    
    /// Return an `Iterator` over the host addresses in this network.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use std::str::FromStr;
    /// # use ipnet::Ipv6Net;
    /// let net = Ipv6Net::from_str("fd00::/126").unwrap();
    /// assert_eq!(net.hosts().collect::<Vec<Ipv6Addr>>(), vec![
    ///     Ipv6Addr::from_str("fd00::").unwrap(),
    ///     Ipv6Addr::from_str("fd00::1").unwrap(),
    ///     Ipv6Addr::from_str("fd00::2").unwrap(),
    ///     Ipv6Addr::from_str("fd00::3").unwrap(),
    /// ]);
    /// ```
    pub fn hosts(&self) -> Ipv6AddrRange {
        Ipv6AddrRange::new(self.network(), self.broadcast())
    }

    /// Returns an `Iterator` over the subnets of this network with the
    /// given prefix length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use ipnet::{Ipv6Net, PrefixLenError};
    /// let net = Ipv6Net::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(18).unwrap().collect::<Vec<Ipv6Net>>(), vec![
    ///     Ipv6Net::from_str("fd00::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:4000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:8000::/18").unwrap(),
    ///     Ipv6Net::from_str("fd00:c000::/18").unwrap(),
    /// ]);
    ///
    /// let net = Ipv6Net::from_str("fd00::/126").unwrap();
    /// assert_eq!(net.subnets(128).unwrap().collect::<Vec<Ipv6Net>>(), vec![
    ///     Ipv6Net::from_str("fd00::/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::1/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::2/128").unwrap(),
    ///     Ipv6Net::from_str("fd00::3/128").unwrap(),
    /// ]);
    ///
    /// let net = Ipv6Net::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(15), Err(PrefixLenError));
    ///
    /// let net = Ipv6Net::from_str("fd00::/16").unwrap();
    /// assert_eq!(net.subnets(129), Err(PrefixLenError));
    /// ```
    pub fn subnets(&self, new_prefix_len: u8) -> Result<Subnets<Ipv6Addr>, PrefixLenError> {
        if self.prefix_len > new_prefix_len || new_prefix_len > 128 {
            return Err(PrefixLenError);
        }
        
        Ok(Subnets::new(
            self.network(),
            self.broadcast(),
            new_prefix_len,
        ))
    }

    // It is significantly faster to work on Emu128 that Ipv6Addr.
    fn interval(&self) -> (Emu128, Emu128) {
        (
            Emu128::from(self.network()),
            Emu128::from(self.broadcast()).saturating_add(Emu128::from(1)),
        )
    }

    /// Aggregate a `Vec` of `Ipv6Net`s and return the result as a new
    /// `Vec`.
    pub fn aggregate(networks: &Vec<Ipv6Net>) -> Vec<Ipv6Net> {
        let mut intervals: Vec<(_, _)> = networks.iter().map(|n| n.interval()).collect();
        intervals = merge_intervals(intervals);
        let mut res: Vec<Ipv6Net> = Vec::new();

        for (start, end) in intervals {
            let iter: Subnets<Ipv6Addr> = Subnets::new(
                start.into(),
                end.saturating_sub(Emu128::from(1)).into(),
                0,
            );

            for n in iter {
                res.push(n);
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

/// An `Iterator` that generates IP network addresses.
///
/// Generates the subnets between the provided `start` and `end` IP
/// addresses inclusive of `end`. Each iteration generates the next
/// network address of the largest valid size it can, while using a
/// prefix lenth not less than `min_prefix_len`.
///
/// # Examples
///
/// ```
/// # use std::net::IpAddr;
/// # use std::str::FromStr;
/// use ipnet::{IpNet, Subnets};
///
/// let subnets = Subnets::new(
///     IpAddr::from_str("10.0.0.0").unwrap(),
///     IpAddr::from_str("10.0.0.239").unwrap(),
///     26,
/// );
/// 
/// assert_eq!(subnets.collect::<Vec<IpNet>>(), vec![
///     IpNet::from_str("10.0.0.0/26").unwrap(),
///     IpNet::from_str("10.0.0.64/26").unwrap(),
///     IpNet::from_str("10.0.0.128/26").unwrap(),
///     IpNet::from_str("10.0.0.192/27").unwrap(),
///     IpNet::from_str("10.0.0.224/28").unwrap(),
/// ]);
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Subnets<T> {
    start: T,
    end: T, // end is inclusive
    min_prefix_len: u8,
}

impl<T> Subnets<T> {
    pub fn new(start: T, end: T, min_prefix_len: u8) -> Self {
        Subnets {
            start: start,
            end: end,
            min_prefix_len: min_prefix_len,
        }
    }
}

fn next_ipv4_subnet(start: Ipv4Addr, end: Ipv4Addr, min_prefix_len: u8) -> Ipv4Net {
    let range = end.saturating_sub(start);
    let range = range.saturating_add(1);
    let range_bits = 32u32.saturating_sub(range.leading_zeros()).saturating_sub(1);
    let start_tz = u32::from(start).trailing_zeros();
    let num_bits = min(range_bits, start_tz);
    let new_prefix_len = 32 - num_bits;
    let next_prefix_len = max(new_prefix_len as u8, min_prefix_len);
    Ipv4Net::new(start, next_prefix_len).unwrap()
}

fn next_ipv6_subnet(start: Ipv6Addr, end: Ipv6Addr, min_prefix_len: u8) -> Ipv6Net {
    let range = end.saturating_sub(start);
    let range = range.saturating_add(Emu128::from(1));    
    let range_bits = 128u32.saturating_sub(range.leading_zeros()).saturating_sub(1);
    let start_tz = Emu128::from(start).trailing_zeros();
    let num_bits = min(range_bits, start_tz);
    let new_prefix_len = 128 - num_bits;
    let next_prefix_len = max(new_prefix_len as u8, min_prefix_len);
    Ipv6Net::new(start, next_prefix_len as u8).unwrap()
}

impl Subnets<IpAddr> {
    fn forward(&mut self) -> IpNet {
        match (self.start, self.end) {
            (IpAddr::V4(start), IpAddr::V4(end)) => {
                let n = IpNet::from(next_ipv4_subnet(start, end, self.min_prefix_len));
                self.start = n.broadcast().saturating_add(1);
                n
            },
            (IpAddr::V6(start), IpAddr::V6(end)) => {
                let n = IpNet::from(next_ipv6_subnet(start, end, self.min_prefix_len));
                self.start = n.broadcast().saturating_add(1);
                n
            },
            _ => unreachable!(),
        }
    }
}

impl Subnets<Ipv4Addr> {
    fn forward(&mut self) -> Ipv4Net {
        let n = next_ipv4_subnet(self.start, self.end, self.min_prefix_len);
        self.start = n.broadcast().saturating_add(1);
        n
    }
}

impl Subnets<Ipv6Addr> {
    fn forward(&mut self) -> Ipv6Net {
        let n = next_ipv6_subnet(self.start, self.end, self.min_prefix_len);
        self.start = n.broadcast().saturating_add(1);
        n
    }
}

macro_rules! subnets_iter_impl {
    ($t:ty, $u:ty) => (
        impl Iterator for Subnets<$t> {
            type Item = $u;

            fn next(&mut self) -> Option<Self::Item> {
                match self.start.partial_cmp(&self.end) {
                    Some(Less) => {
                        let n = self.forward();
                        // Stop the iterator if we saturated self.start.
                        // This check worsens performance slightly but
                        // overall operating on IpAddr types is faster.
                        if self.start == n.broadcast() {
                            self.end.replace_zero();
                        }
                        Some(n)
                    },
                    Some(Equal) => {
                        let n = self.forward();
                        self.end.replace_zero();
                        Some(n)
                    },
                    _ => None,
                }
            }
        }
    )
}

subnets_iter_impl!(IpAddr, IpNet);
subnets_iter_impl!(Ipv4Addr, Ipv4Net);
subnets_iter_impl!(Ipv6Addr, Ipv6Net);

// Generic function for merging a vector of intervals.
fn merge_intervals<T: Copy + Ord>(mut intervals: Vec<(T, T)>) -> Vec<(T, T)> {
    if intervals.len() == 0 {
        return intervals;
    }

    intervals.sort();
    let mut res: Vec<(T, T)> = Vec::new();
    let (mut start, mut end) = intervals[0];
    
    let mut i = 1;
    let len = intervals.len();
    while i < len {
        let (next_start, next_end) = intervals[i];
        if end >= next_start {
            start = min(start, next_start);
            end = max(end, next_end);
        }
        else {
            res.push((start, end));
            start = next_start;
            end = next_end;
        }
        i += 1;
    }

    res.push((start, end));
    res
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use super::*;

    #[test]
    fn test_merge_intervals() {
        let v = vec![
            (0, 1), (1, 2), (2, 3),
            (11, 12), (13, 14), (10, 15), (11, 13),
            (20, 25), (24, 29),
        ];

        let v_ok = vec![
            (0, 3),
            (10, 15),
            (20, 29),
        ];

        let vv = vec![
            ([0, 1], [0, 2]), ([0, 2], [0, 3]), ([0, 0], [0, 1]),
            ([10, 15], [11, 0]), ([10, 0], [10, 16]),
        ];

        let vv_ok = vec![
            ([0, 0], [0, 3]),
            ([10, 0], [11, 0]),
        ];

        assert_eq!(merge_intervals(v), v_ok);
        assert_eq!(merge_intervals(vv), vv_ok);
    }

    macro_rules! ipnet_vec {
        ($($x:expr),*) => ( vec![$(IpNet::from_str($x).unwrap(),)*] );
        ($($x:expr,)*) => ( ipnet_vec![$($x),*] );
    }

    macro_rules! make_subnets_test {
        ($name:ident, $start:expr, $end:expr, $min_prefix_len:expr, $($x:expr),*) => (
            #[test]
            fn $name() {
                let subnets = Subnets::<IpAddr>::new(
                    IpAddr::from_str($start).unwrap(),
                    IpAddr::from_str($end).unwrap(),
                    $min_prefix_len,
                );
                let results = ipnet_vec![$($x),*];
                assert_eq!(subnets.collect::<Vec<IpNet>>(), results);
            }
        );
        ($name:ident, $start:expr, $end:expr, $min_prefix_len:expr, $($x:expr,)*) => (
            make_subnets_test!($name, $start, $end, $min_prefix_len, $($x),*);
        );
    }

    make_subnets_test!(
        test_subnets_zero_zero,
        "0.0.0.0", "0.0.0.0", 0,
        "0.0.0.0/32",
    );

    make_subnets_test!(
        test_subnets_max_max,
        "255.255.255.255", "255.255.255.255", 0,
        "255.255.255.255/32",
    );
    
    make_subnets_test!(
        test_subnets_none,
        "0.0.0.1", "0.0.0.0", 0,
    );
    
    make_subnets_test!(
        test_subnets_one,
        "0.0.0.0", "0.0.0.1", 0,
        "0.0.0.0/31",
    );

    make_subnets_test!(
        test_subnets_two,
        "0.0.0.0", "0.0.0.2", 0,
        "0.0.0.0/31",
        "0.0.0.2/32",
    );
    
    make_subnets_test!(
        test_subnets_taper,
        "0.0.0.0", "0.0.0.10", 30,
        "0.0.0.0/30",
        "0.0.0.4/30",
        "0.0.0.8/31",
        "0.0.0.10/32",
    );

    #[test]
    fn test_aggregate() {
        let ip_nets = ipnet_vec![
            "10.0.0.0/24", "10.0.1.0/24", "10.0.1.1/24", "10.0.1.2/24",
            "10.0.2.0/24",
            "10.1.0.0/24", "10.1.1.0/24",
            "192.168.0.0/24", "192.168.1.0/24", "192.168.2.0/24", "192.168.3.0/24",
            "fd00::/32", "fd00:1::/32",
            "fd00:2::/32",
        ];

        let ip_aggs = ipnet_vec![
            "10.0.0.0/23",
            "10.0.2.0/24",
            "10.1.0.0/23",
            "192.168.0.0/22",
            "fd00::/31",
            "fd00:2::/32",
        ];

        let ipv4_nets: Vec<Ipv4Net> = ip_nets.iter().filter_map(|p| if let IpNet::V4(x) = *p { Some(x) } else { None }).collect();
        let ipv4_aggs: Vec<Ipv4Net> = ip_aggs.iter().filter_map(|p| if let IpNet::V4(x) = *p { Some(x) } else { None }).collect();
        let ipv6_nets: Vec<Ipv6Net> = ip_nets.iter().filter_map(|p| if let IpNet::V6(x) = *p { Some(x) } else { None }).collect();
        let ipv6_aggs: Vec<Ipv6Net> = ip_aggs.iter().filter_map(|p| if let IpNet::V6(x) = *p { Some(x) } else { None }).collect();

        assert_eq!(IpNet::aggregate(&ip_nets), ip_aggs);
        assert_eq!(Ipv4Net::aggregate(&ipv4_nets), ipv4_aggs);
        assert_eq!(Ipv6Net::aggregate(&ipv6_nets), ipv6_aggs);
    }
}
