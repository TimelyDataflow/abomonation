extern crate abomonation;

use abomonation::*;

#[test] fn test_array() { _test_pass(vec![[0, 1, 2]; 1024]); }
#[test] fn test_nonzero() { _test_pass(vec![[std::num::NonZeroI32::new(1)]; 1024]); }
#[test] fn test_opt_vec() { _test_pass(vec![Some(vec![0,1,2]), None]); }
#[test] fn test_alignment() { _test_pass(vec![(format!("x"), vec![1,2,3]); 1024]); }
#[test] fn test_alignment_128() { _test_pass(vec![(format!("x"), vec![1u128,2,3]); 1024]); }
#[test] fn test_option_box_u64() { _test_pass(vec![Some(Box::new(0u64))]); }
#[test] fn test_option_vec() { _test_pass(vec![Some(vec![0, 1, 2])]); }
#[test] fn test_u32x4_pass() { _test_pass(vec![((1,2,3),vec![(0u32, 0u32, 0u32, 0u32); 1024])]); }
#[test] fn test_u64_pass() { _test_pass(vec![0u64; 1024]); }
#[test] fn test_u128_pass() { _test_pass(vec![0u128; 1024]); }
#[test] fn test_string_pass() { _test_pass(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_pass() { _test_pass(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[test] fn test_u64_fail() { _test_fail(vec![0u64; 1024]); }
#[test] fn test_u128_fail() { _test_fail(vec![0u128; 1024]); }
#[test] fn test_string_fail() { _test_fail(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_fail() { _test_fail(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[test] fn test_array_size() { _test_size(vec![[0, 1, 2]; 1024]); }
#[test] fn test_opt_vec_size() { _test_size(vec![Some(vec![0,1,2]), None]); }
#[test] fn test_alignment_size() { _test_size(vec![(format!("x"), vec![1,2,3]); 1024]); }
#[test] fn test_option_box_u64_size() { _test_size(vec![Some(Box::new(0u64))]); }
#[test] fn test_option_vec_size() { _test_size(vec![Some(vec![0, 1, 2])]); }
#[test] fn test_u32x4_size() { _test_size(vec![((1,2,3),vec![(0u32, 0u32, 0u32, 0u32); 1024])]); }
#[test] fn test_u64_size() { _test_size(vec![0u64; 1024]); }
#[test] fn test_u128_size() { _test_size(vec![0u128; 1024]); }
#[test] fn test_string_size() { _test_size(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_size() { _test_size(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[test]
fn test_phantom_data_for_non_abomonatable_type() {
    use std::marker::PhantomData;
    struct NotAbomonatable;
    _test_pass(PhantomData::<NotAbomonatable>::default());
}

fn _test_pass<T: Abomonation+Eq>(record: T) {
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }
    {
        let (result, rest) = unsafe { decode::<T>(&mut bytes[..]) }.unwrap();
        assert!(&record == result);
        assert!(rest.len() == 0);
    }
}

fn _test_fail<T: Abomonation>(record: T) {
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }
    bytes.pop();
    assert!(unsafe { decode::<T>(&mut bytes[..]) }.is_none());
}

fn _test_size<T: Abomonation>(record: T) {
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }
    assert_eq!(bytes.len(), measure(&record));
}


#[derive(Eq, PartialEq)]
struct MyStruct {
    a: String,
    b: u64,
    c: Vec<u8>,
}

unsafe_abomonate!(MyStruct : a, b, c);

#[test]
fn test_macro() {
    // create some test data out of abomonation-approved types
    let record = MyStruct{ a: "test".to_owned(), b: 0, c: vec![0, 1, 2] };

    // encode vector into a Vec<u8>
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // decode a &Vec<(u64, String)> from binary data
    if let Some((result, rest)) = unsafe { decode::<MyStruct>(&mut bytes) } {
        assert!(result == &record);
        assert!(rest.len() == 0);
    }
}

#[test]
fn test_macro_size() {
    // create some test data out of abomonation-approved types
    let record = MyStruct{ a: "test".to_owned(), b: 0, c: vec![0, 1, 2] };

    // encode vector into a Vec<u8>
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }
    assert_eq!(bytes.len(), measure(&record));
}

#[test]
fn test_multiple_encode_decode() {
    let mut bytes = Vec::new();
    unsafe { encode(&0u32, &mut bytes).unwrap(); }
    unsafe { encode(&7u64, &mut bytes).unwrap(); }
    unsafe { encode(&vec![1,2,3], &mut bytes).unwrap(); }
    unsafe { encode(&"grawwwwrr".to_owned(), &mut bytes).unwrap(); }

    let (t, r) = unsafe { decode::<u32>(&mut bytes) }.unwrap(); assert!(*t == 0);
    let (t, r) = unsafe { decode::<u64>(r) }.unwrap(); assert!(*t == 7);
    let (t, r) = unsafe { decode::<Vec<i32>>(r) }.unwrap(); assert!(*t == vec![1,2,3]);
    let (t, _r) = unsafe { decode::<String>(r) }.unwrap(); assert!(*t == "grawwwwrr".to_owned());
}

#[test]
fn test_net_types() {

    use std::net::{SocketAddr, IpAddr, Ipv4Addr, Ipv6Addr};

    let socket_addr4 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(128, 0, 0, 1)), 1234);
    let socket_addr6 = SocketAddr::new(IpAddr::V6(Ipv6Addr::LOCALHOST), 1234);

    let mut bytes = Vec::new();

    unsafe { encode(&socket_addr4, &mut bytes).unwrap(); }
    unsafe { encode(&socket_addr6, &mut bytes).unwrap(); }

    let (t, r) = unsafe { decode::<SocketAddr>(&mut bytes) }.unwrap(); assert!(*t == socket_addr4);
    let (t, _r) = unsafe { decode::<SocketAddr>(r) }.unwrap(); assert!(*t == socket_addr6);
}

#[test]
fn test_ref_types() {
    use std::sync::Arc;
    let value = Arc::new("hello".to_owned());

    let mut bytes = Vec::new();
    unsafe { abomonation::encode(&value, &mut bytes).unwrap() };
    // abomonated bytes end with "hello"
    assert_eq!(&bytes[bytes.len() - 5..], b"hello");

    let mut reference = Vec::new();
    unsafe { abomonation::encode(&"hello".to_owned(), &mut reference).unwrap() };
    // abomonating an Arc is like abomonating a pointer and then the contained value
    assert_eq!(&bytes[std::mem::size_of::<usize>() + 2..], &reference[2..]);

    // modify the bytes to see that deserialization uses them and not the pointer
    let pos = bytes.len() - 4;
    bytes[pos] = b'a';

    let (value2, bytes) = unsafe { abomonation::decode::<Arc<String>>(&mut bytes).unwrap() };
    assert_eq!(value2.as_ref(), "hallo");
    assert!(bytes.is_empty());
}