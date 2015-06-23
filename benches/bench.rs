#![feature(test)]

extern crate abomonation;
extern crate test;

use abomonation::*;
use test::Bencher;


use std::io::Read;

#[bench] fn enc_u64(bencher: &mut Bencher) { _bench_enc(bencher, &vec![0u64; 1024]); }
#[bench] fn dec_u64(bencher: &mut Bencher) { _bench_dec(bencher, &vec![0u64; 1024]); }

#[bench] fn enc_string(bencher: &mut Bencher) { _bench_enc(bencher, &vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn dec_string(bencher: &mut Bencher) { _bench_dec(bencher, &vec![format!("grawwwwrr!"); 1024]); }

#[bench] fn enc_vec_u_s(bencher: &mut Bencher) { _bench_enc(bencher, &vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn dec_vec_u_s(bencher: &mut Bencher) { _bench_dec(bencher, &vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

fn _bench_enc<T: Abomonation>(bencher: &mut Bencher, vector: &Vec<T>) {

    let mut bytes = Vec::new();
    encode(vector, &mut bytes);

    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        bytes.clear();
        encode(&vector[..], &mut bytes);
    });
}

fn _bench_dec<T: Abomonation+Eq>(bencher: &mut Bencher, vector: &Vec<T>) {

    let mut bytes = Vec::new();
    encode(&vector[..], &mut bytes);

    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        let result = decode::<T>(&mut bytes[..]).unwrap();

        assert!(result.len() == vector.len());
        for i in 0..result.len() {
            assert!(result[i] == vector[i]);
        }
    });
}
