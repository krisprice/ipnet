#![cfg(all(feature = "serde", any(feature = "heapless", feature = "ser_as_str")))]

use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use serde::Serialize;
use serde_test::{assert_ser_tokens, Configure, Token};

fn assert_no_formatting_allocations<T: Serialize>(net: T, text: &'static str) {
    let allocations = allocation_counter::measure(|| {
        assert_ser_tokens(&net.readable(), &[Token::Str(text)]);
    });
    assert_eq!(allocations.count_total, 0, "formatting {} allocated", text);
}

#[test]
fn human_readable_serialization_does_not_allocate() {
    for text in &["0.0.0.0/0", "192.168.0.0/24", "255.255.255.255/32"] {
        let net: Ipv4Net = text.parse().unwrap();
        assert_no_formatting_allocations(net, text);
        assert_no_formatting_allocations(IpNet::from(net), text);
    }
    for text in &[
        "::/0",
        "::ffff:192.0.2.1/128",
        "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/128",
    ] {
        let net: Ipv6Net = text.parse().unwrap();
        assert_no_formatting_allocations(net, text);
        assert_no_formatting_allocations(IpNet::from(net), text);
    }
}
