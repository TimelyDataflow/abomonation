#[macro_use]
extern crate abomonation;
use abomonation::*;

#[test] fn test_option_box_u64() { _test_pass(vec![Some(Box::new(0u64))]); }
#[test] fn test_option_vec() { _test_pass(vec![Some(vec![0, 1, 2])]); }
#[test] fn test_u32x4_pass() { _test_pass(vec![((1,2,3),vec![(0u32, 0u32, 0u32, 0u32); 1024])]); }
#[test] fn test_u64_pass() { _test_pass(vec![0u64; 1024]); }
#[test] fn test_string_pass() { _test_pass(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_pass() { _test_pass(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[test] fn test_u64_fail() { _test_fail(vec![0u64; 1024]); }
#[test] fn test_string_fail() { _test_fail(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_fail() { _test_fail(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

fn _test_pass<T: Abomonation+Eq>(record: T) {
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);
    let (result, rest) = decode::<T>(&mut bytes[..]).unwrap();
    assert!(&record == result);
    assert!(rest.len() == 0);
}

fn _test_fail<T: Abomonation>(record: T) {
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);
    bytes.pop();
    assert!(decode::<T>(&mut bytes[..]).is_none());
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
    encode(&record, &mut bytes);

    // decode a &Vec<(u64, String)> from binary data
    if let Some((result, rest)) = decode::<MyStruct>(&mut bytes) {
        assert!(result == &record);
        assert!(rest.len() == 0);
    }
}

#[test]
fn test_multiple_encode_decode() {
    let mut bytes = Vec::new();
    encode(&0u32, &mut bytes);
    encode(&7u64, &mut bytes);
    encode(&vec![1,2,3], &mut bytes);
    encode(&"grawwwwrr".to_owned(), &mut bytes);

    let (t, r) = decode::<u32>(&mut bytes).unwrap(); assert!(*t == 0);
    let (t, r) = decode::<u64>(r).unwrap(); assert!(*t == 7);
    let (t, r) = decode::<Vec<i32>>(r).unwrap(); assert!(*t == vec![1,2,3]);
    let (t, _r) = decode::<String>(r).unwrap(); assert!(*t == "grawwwwrr".to_owned());
}
