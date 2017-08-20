use std;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use emu128::emu128;

/// Convert an emulated u128 to an Ipv6Addr.
///
/// TODO: It would be nice to implement From on Ipv6Addr for this.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::ipv6_addr_from_double_u64;
/// assert_eq!(ipv6_addr_from_double_u64([0u64, 1u64]), Ipv6Addr::from_str("::1").unwrap());
/// ```
pub fn ipv6_addr_from_emu128(ip: emu128) -> Ipv6Addr {
    Ipv6Addr::new(
        (ip.hi >> 48) as u16, (ip.hi >> 32) as u16, (ip.hi >> 16) as u16, ip.hi as u16,
        (ip.lo >> 48) as u16, (ip.lo >> 32) as u16, (ip.lo >> 16) as u16, ip.lo as u16
    )
}

/// Convert an Ipv6Addr to an emulated u128.
///
/// TODO: It would be nice to implement From on Ipv6Addr for this.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
/// use std::str::FromStr;
/// use ipnet::ipv6_addr_into_double_u64;
/// assert_eq!(ipv6_addr_into_double_u64(Ipv6Addr::from_str("::1").unwrap()), [0u64, 1u64]);
/// ```
pub fn ipv6_addr_into_emu128(ip: Ipv6Addr) -> emu128 {
    let ip = ip.octets();
    emu128 {
        hi: ((ip[0] as u64) << 56) + ((ip[1] as u64) << 48) +
            ((ip[2] as u64) << 40) + ((ip[3] as u64) << 32) +
            ((ip[4] as u64) << 24) + ((ip[5] as u64) << 16) +
            ((ip[6] as u64) << 8) + (ip[7] as u64),
        lo: ((ip[8] as u64) << 56) + ((ip[9] as u64) << 48) +
            ((ip[10] as u64) << 40) + ((ip[11] as u64) << 32) +
            ((ip[12] as u64) << 24) + ((ip[13] as u64) << 16) +
            ((ip[14] as u64) << 8) + (ip[15] as u64),
    }
}

pub trait IpAdd<RHS = Self> {
    type Output;
    fn add(self, rhs: RHS) -> Self::Output;
}

pub trait IpSub<RHS = Self> {
    type Output;
    fn sub(self, rhs: RHS) -> Self::Output;
}

pub trait IpBitAnd<RHS = Self> {
    type Output;
    fn bitand(self, rhs: RHS) -> Self::Output;
}

pub trait IpBitOr<RHS = Self> {
    type Output;
    fn bitor(self, rhs: RHS) -> Self::Output;
}

macro_rules! ip_add_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpAdd<$f> for $t {
            type Output = $t;
            #[inline]
            fn add(self, rhs: $f) -> $t {
                Self::from(u32::from(self).saturating_add(u32::from(rhs)))
            }
        }
    )*
    }
}

ip_add_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_sub_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpSub<$f> for $t {
            type Output = $t;
            #[inline]
            fn sub(self, rhs: $f) -> $t {
                Self::from(u32::from(self).saturating_sub(u32::from(rhs)))
            }
        }
    )*
    }
}

ip_sub_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_bitand_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitAnd<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitand(self, rhs: $f) -> $t {
                Self::from(u32::from(self) & u32::from(rhs))
            }
        }
    )*
    }
}

ip_bitand_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }

macro_rules! ip_bitor_impl {
    ($(($t:ty, $f:ty),)*) => {
    $(
        impl IpBitOr<$f> for $t {
            type Output = $t;
            #[inline]
            fn bitor(self, rhs: $f) -> $t {
                Self::from(u32::from(self) | u32::from(rhs))
            }
        }
    )*
    }
}

ip_bitor_impl! { (Ipv4Addr, Ipv4Addr), (Ipv4Addr, u32), }
