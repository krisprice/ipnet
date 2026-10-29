#![cfg(all(feature = "serde", any(feature = "schemars08", feature = "schemars1")))]

use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use serde_json::Value;

fn check_schemas(ip: Value, v4: Value, v6: Value) {
    let ip = jsonschema::validator_for(&ip).unwrap();
    let v4 = jsonschema::validator_for(&v4).unwrap();
    let v6 = jsonschema::validator_for(&v6).unwrap();

    for text in &["0.0.0.0/0", "192.168.0.0/24", "255.255.255.255/32"] {
        let net: Ipv4Net = text.parse().unwrap();
        let value = serde_json::to_value(net).unwrap();
        assert!(v4.is_valid(&value), "IPv4 schema rejects {}", text);
        assert!(!v6.is_valid(&value), "IPv6 schema accepts {}", text);
        let value = serde_json::to_value(IpNet::from(net)).unwrap();
        assert!(ip.is_valid(&value), "IpNet schema rejects {}", text);
    }

    for text in &[
        "::/0",
        "fd00::/32",
        "::ffff:192.0.2.1/128",
        "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/128",
    ] {
        let net: Ipv6Net = text.parse().unwrap();
        let value = serde_json::to_value(net).unwrap();
        assert!(v6.is_valid(&value), "IPv6 schema rejects {}", text);
        assert!(!v4.is_valid(&value), "IPv4 schema accepts {}", text);
        let value = serde_json::to_value(IpNet::from(net)).unwrap();
        assert!(ip.is_valid(&value), "IpNet schema rejects {}", text);
    }

    for text in &["192.168.0.0/33", "fd00::/129", "not a network"] {
        assert!(!ip.is_valid(&Value::from(*text)));
    }
}

#[test]
#[cfg(feature = "schemars08")]
fn serialized_networks_match_schemars08() {
    check_schemas(
        serde_json::to_value(schemars08::schema_for!(IpNet)).unwrap(),
        serde_json::to_value(schemars08::schema_for!(Ipv4Net)).unwrap(),
        serde_json::to_value(schemars08::schema_for!(Ipv6Net)).unwrap(),
    );
}

#[test]
#[cfg(feature = "schemars1")]
fn serialized_networks_match_schemars1() {
    check_schemas(
        serde_json::to_value(schemars1::schema_for!(IpNet)).unwrap(),
        serde_json::to_value(schemars1::schema_for!(Ipv4Net)).unwrap(),
        serde_json::to_value(schemars1::schema_for!(Ipv6Net)).unwrap(),
    );
}
