use {Ipv4Net, Ipv6Net};
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};

impl<'de> Deserialize<'de> for Ipv4Net {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        String::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

impl Serialize for Ipv4Net {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for Ipv6Net {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        String::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

impl Serialize for Ipv6Net {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(test)]
mod tests {
    extern crate serde_test;

    use {IpNet, Ipv4Net, Ipv6Net};
    use self::serde_test::{assert_tokens, Configure, Token};

    #[test]
    fn test_serialize_ipv4_net() {
        let net_str = "10.1.1.0/24";
        let net: Ipv4Net = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
    }

    #[test]
    fn test_serialize_ipnet_v4() {
        let net_str = "10.1.1.0/24";
        let net: IpNet = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
    }

    #[test]
    fn test_serialize_ipv6_net() {
        let net_str = "fd00::/32";
        let net: Ipv6Net = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
    }

    #[test]
    fn test_serialize_ipnet_v6() {
        let net_str = "fd00::/32";
        let net: IpNet = net_str.parse().unwrap();
        assert_tokens(&net.readable(), &[Token::Str(net_str)]);
    }
}
