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
    let result = decode::<T>(&mut bytes[..]).unwrap();
    assert!(&record == result);
}

fn _test_fail<T: Abomonation>(record: T) {
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);
    bytes.pop();
    if let Ok(_) = decode::<T>(&mut bytes[..]) { panic!() }
    else { }
}

#[derive(Eq, PartialEq)]
struct MyStruct {
    a: String,
    b: u64,
    c: Vec<u8>,
}

abomonate!(MyStruct : a, b, c);

#[test]
fn test_macro() {
    // create some test data out of abomonation-approved types
    let record = MyStruct{ a: "test".to_owned(), b: 0, c: vec![0, 1, 2] };

    // encode vector into a Vec<u8>
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);

    // decode a &Vec<(u64, String)> from binary data
    if let Ok(result) = decode::<MyStruct>(&mut bytes) {
        assert!(result == &record);
    }
}
