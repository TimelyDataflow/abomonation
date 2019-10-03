extern crate abomonation;

use abomonation::*;
use std::fmt::Debug;

// Test struct for the unsafe_abomonate macro
#[derive(Clone, Debug, Eq, PartialEq)]
struct MyStruct {
    a: String,
    b: u64,
    c: Vec<u8>,
}
unsafe_abomonate!(MyStruct : a, b, c);

// Test for PhantomData abomonation, which has no Abomonation bound
struct NotAbomonatable;
type PhantomNotAbo = std::marker::PhantomData::<NotAbomonatable>;

// Generic serialization/deserialization testing procedure, add your data here.
macro_rules! gen_tests {
    (
        $( $data:expr => ($pass:ident, $fail:ident, $size:ident) ), *$(,)*
    ) => {
        $(
            #[test] fn $pass() { _test_pass(&mut Vec::new(), vec![$data; 1024]); }
            #[test] fn $fail() { _test_fail(&mut Vec::new(), vec![$data; 1024]); }
            #[test] fn $size() { _test_size(&mut Vec::new(), vec![$data; 1024]); }
        )*
    };
}
gen_tests!{
    [4, 1, 2] => (test_array_pass,
                  test_array_fail,
                  test_array_size),

    std::num::NonZeroI32::new(1) => (test_nonzero_pass,
                                     test_nonzero_fail,
                                     test_nonzero_size),

    Some(vec![8, 1, 2]) => (test_option_vec_pass,
                            test_option_vec_fail,
                            test_option_vec_size),

    (format!("x"), vec![1, 2, 3])  => (test_alignment_pass,
                                       test_alignment_fail,
                                       test_alignment_size),

    (format!("x"), vec![1u128, 2, 3]) => (test_alignment_128_pass,
                                          test_alignment_128_fail,
                                          test_alignment_128_size),

    Some(Box::new(9u64)) => (test_option_box_u64_pass,
                             test_option_box_u64_fail,
                             test_option_box_u64_size),

    (3u32, 8u32, 1u32, 7u32) => (test_u32x4_pass,
                                 test_u32x4_fail,
                                 test_u32x4_size),

    42u64 => (test_u64_pass,
              test_u64_fail,
              test_u64_size),

    687u128 => (test_u128_pass,
                test_u128_fail,
                test_u128_size),

    format!("grawwwwrr!") => (test_string_pass,
                              test_string_fail,
                              test_string_size),

    vec![(0u64, format!("grawwwwrr!")); 32] => (test_vec_u_s_pass,
                                                test_vec_u_s_fail,
                                                test_vec_u_s_size),

    MyStruct{ a: "test".to_owned(),
              b: 0,
              c: vec![0, 1, 2] } => (test_macro_pass,
                                     test_macro_fail,
                                     test_macro_size),

    PhantomNotAbo::default() => (test_phantom_notabo_pass,
                                 test_phantom_notabo_fail,
                                 test_phantom_notabo_size),

    Some(&42u64) => (test_ref_u64_pass,
                     test_ref_u64_fail,
                     test_ref_u64_size),
}

// FIXME: I could not find an API which allows _test_pass to allocate a Vec
//        internally without restricting the set of allowed Abomonation impls.
fn _test_pass<'bytes, T>(mut bytes: &'bytes mut Vec<u8>, record: T)
    where T: Abomonation<'bytes> + Debug + Eq
{
    unsafe { encode(&record, &mut bytes).unwrap(); }
    {
        let (result, rest) = unsafe { decode::<T>(&mut bytes[..]) }.unwrap();
        assert_eq!(&record, result);
        assert_eq!(rest.len(), 0);
    }
}

// FIXME: I could not find an API which allows _test_fail to allocate a Vec
//        internally without restricting the set of allowed Abomonation impls.
fn _test_fail<'bytes, T>(mut bytes: &'bytes mut Vec<u8>, record: T)
    where T: Abomonation<'bytes> + Debug + Eq
{
    unsafe { encode(&record, &mut bytes).unwrap(); }
    if bytes.pop().is_some() {
        assert_eq!(unsafe { decode::<T>(&mut bytes[..]) }, None);
    }
}

// FIXME: I could not find an API which allows _test_size to allocate a Vec
//        internally without restricting the set of allowed Abomonation impls.
fn _test_size<'bytes, T: Abomonation<'bytes>>(mut bytes: &'bytes mut Vec<u8>, record: T) {
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

    let (t, r) = unsafe { decode::<u32>(&mut bytes) }.unwrap(); assert_eq!(*t, 0);
    let (t, r) = unsafe { decode::<u64>(r) }.unwrap(); assert_eq!(*t, 7);
    let (t, r) = unsafe { decode::<Vec<i32>>(r) }.unwrap(); assert_eq!(*t, vec![1,2,3]);
    let (t, _r) = unsafe { decode::<String>(r) }.unwrap(); assert_eq!(*t, "grawwwwrr".to_owned());
}

#[test]
fn test_net_types() {

    use std::net::{SocketAddr, IpAddr, Ipv4Addr, Ipv6Addr};

    let socket_addr4 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(128, 0, 0, 1)), 1234);
    let socket_addr6 = SocketAddr::new(IpAddr::V6(Ipv6Addr::LOCALHOST), 1234);

    let mut bytes = Vec::new();

    unsafe { encode(&socket_addr4, &mut bytes).unwrap(); }
    unsafe { encode(&socket_addr6, &mut bytes).unwrap(); }

    let (t, r) = unsafe { decode::<SocketAddr>(&mut bytes) }.unwrap(); assert_eq!(*t, socket_addr4);
    let (t, _r) = unsafe { decode::<SocketAddr>(r) }.unwrap(); assert_eq!(*t, socket_addr6);
}
