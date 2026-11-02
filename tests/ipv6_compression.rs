use ipnet::{IpNet, Ipv6Net};
use std::net::Ipv6Addr;

fn check_address(address: &str) {
    let expected = address.parse::<Ipv6Addr>();
    for prefix in [0, 64, 128] {
        let cidr = format!("{address}/{prefix}");
        match expected {
            Ok(addr) => {
                let network = Ipv6Net::new(addr, prefix).unwrap();
                assert_eq!(cidr.parse::<Ipv6Net>(), Ok(network), "{cidr}");
                assert_eq!(cidr.parse::<IpNet>(), Ok(IpNet::V6(network)), "{cidr}");
            }
            Err(_) => {
                assert!(cidr.parse::<Ipv6Net>().is_err(), "accepted {}", cidr);
                assert!(cidr.parse::<IpNet>().is_err(), "accepted {}", cidr);
            }
        }
    }
}

#[test]
fn compression_requires_at_least_one_omitted_group() {
    // Exercise a compression marker at every position, from an all-zero address
    // through seven explicit groups (valid) and eight or more (invalid).
    for groups in 0..=9 {
        for head in 0..=groups {
            let leading = vec!["ffff"; head].join(":");
            let trailing = vec!["ffff"; groups - head].join(":");
            check_address(&format!("{leading}::{trailing}"));
        }
    }
    check_address("1:2:3:4:5:6:7:8");
}

#[test]
fn compression_counts_embedded_ipv4_as_two_groups() {
    for groups in 0..=7 {
        let leading = vec!["ffff"; groups].join(":");
        check_address(&format!("{leading}::192.0.2.1"));
    }
    check_address("1:2:3:4:5:6:192.0.2.1");
}

#[test]
#[cfg(feature = "serde")]
fn human_readable_deserialization_checks_compression() {
    use serde_test::{assert_de_tokens_error, assert_tokens, Configure, Readable, Token};

    for cidr in [
        "ffff:ffff:ffff:ffff:ffff:ffff::ffff:ffff/114",
        "1:2:3:4:5:6::192.0.2.1/128",
    ] {
        assert_de_tokens_error::<Readable<Ipv6Net>>(
            &[Token::Str(cidr)],
            "invalid IP address syntax",
        );
        assert_de_tokens_error::<Readable<IpNet>>(&[Token::Str(cidr)], "invalid IP address syntax");
    }
    let cidr = "::ffff:192.0.2.1/128";
    let network: Ipv6Net = cidr.parse().unwrap();
    assert_tokens(&network.readable(), &[Token::Str(cidr)]);
    assert_tokens(&IpNet::V6(network).readable(), &[Token::Str(cidr)]);
}
