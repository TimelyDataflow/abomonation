extern crate abomonation;
use abomonation::*;

#[test] fn test_option_vec() { _test_pass(vec![Some(vec![0, 1, 2])]); }
#[test] fn test_u32x4_pass() { _test_pass(vec![((1,2,3),vec![(0u32, 0u32, 0u32, 0u32); 1024])]); }
#[test] fn test_u64_pass() { _test_pass(vec![0u64; 1024]); }
#[test] fn test_string_pass() { _test_pass(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_pass() { _test_pass(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[test] fn test_u64_fail() { _test_fail(vec![0u64; 1024]); }
#[test] fn test_string_fail() { _test_fail(vec![format!("grawwwwrr!"); 1024]); }
#[test] fn test_vec_u_s_fail() { _test_fail(vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

fn _test_pass<T: Abomonation+Eq>(vector: Vec<T>) {
    let mut bytes = Vec::new();
    encode(&vector, &mut bytes);
    let result = decode::<Vec<T>>(&mut bytes[..]).unwrap();
    assert!(result.len() == vector.len());
    for i in 0..result.len() {
        assert!(result[i] == vector[i]);
    }
}

fn _test_fail<T: Abomonation>(vector: Vec<T>) {
    let mut bytes = Vec::new();
    encode(&vector, &mut bytes);
    bytes.pop();
    if let Ok(_) = decode::<Vec<T>>(&mut bytes[..]) { panic!() }
    else { }
}
