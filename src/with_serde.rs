use {IpNet, Ipv4Net, Ipv6Net};
use std::net::{Ipv4Addr, Ipv6Addr};
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};

impl<'de> Deserialize<'de> for Ipv4Net {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        if deserializer.is_human_readable() {
            String::deserialize(deserializer)?
                .parse()
                .map_err(serde::de::Error::custom)
        } else {
            // TODO: Error if not correct number of bytes?
            let b = <&[u8]>::deserialize(deserializer)?;
            Ipv4Net::new(Ipv4Addr::new(b[0], b[1], b[2], b[3]), b[4]).map_err(serde::de::Error::custom)
        }
    }
}

impl Serialize for Ipv4Net {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&self.to_string())
        } else {
            let mut v: Vec<u8> = vec![];
            v.extend_from_slice(&self.octets());
            v.push(self.prefix_len());
            serializer.serialize_bytes(&v)
        }
    }
}

impl<'de> Deserialize<'de> for Ipv6Net {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        if deserializer.is_human_readable() {
            String::deserialize(deserializer)?
                .parse()
                .map_err(serde::de::Error::custom)
        } else {
            // TODO: Error if not correct number of bytes?
            let b = <&[u8]>::deserialize(deserializer)?;
            Ipv6Net::new(Ipv6Addr::new(
                ((b[0] as u16) << 8) | b[1] as u16, ((b[2] as u16) << 8) | b[3] as u16,
                ((b[4] as u16) << 8) | b[5] as u16, ((b[6] as u16) << 8) | b[7] as u16,
                ((b[8] as u16) << 8) | b[9] as u16, ((b[10] as u16) << 8) | b[11] as u16,
                ((b[12] as u16) << 8) | b[13] as u16, ((b[14] as u16) << 8) | b[15] as u16
            ), b[16]).map_err(serde::de::Error::custom)
        }
    }
}

impl Serialize for Ipv6Net {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&self.to_string())
        } else {
            let mut v: Vec<u8> = vec![];
            v.extend_from_slice(&self.octets());
            v.push(self.prefix_len());
            serializer.serialize_bytes(&v)
        }
    }
}

impl<'de> Deserialize<'de> for IpNet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            String::deserialize(deserializer)?
                .parse()
                .map_err(serde::de::Error::custom)
        } else {
            unimplemented!();
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate serde_test;

    use {IpNet, Ipv4Net, Ipv6Net};
    use self::serde_test::{assert_tokens, assert_ser_tokens, assert_de_tokens, Configure, Token};

    // TODO: test deserialization when implemented. Test vectors of
    // network addresses.

    #[test]
    fn test_serialize_ipv4_net() {
        let net_str = "10.1.1.0/24";
        let net: Ipv4Net = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
        assert_ser_tokens(&net.compact(), &[Token::Bytes(&[10u8, 1, 1, 0, 24])]);
    }

    #[test]
    fn test_serialize_ipnet_v4() {
        let net_str = "10.1.1.0/24";
        let net: IpNet = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
        assert_ser_tokens(&net.compact(), &[Token::Bytes(&[10u8, 1, 1, 0, 24])]);
    }

    #[test]
    fn test_serialize_ipv6_net() {
        let net_str = "fd00::/32";
        let net: Ipv6Net = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
        assert_ser_tokens(&net.compact(), &[Token::Bytes(&[253u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32])]);
    }

    #[test]
    fn test_serialize_ipnet_v6() {
        let net_str = "fd00::/32";
        let net: IpNet = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
        assert_ser_tokens(&net.compact(), &[Token::Bytes(&[253u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32])]);
    }
}