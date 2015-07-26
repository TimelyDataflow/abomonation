#![feature(test)]

extern crate abomonation;
extern crate test;

use abomonation::*;
use test::Bencher;
use std::io::Read;

#[bench] fn empty_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![(); 1024]); }
#[bench] fn empty_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![(); 1024]); }
#[bench] fn empty_own(bencher: &mut Bencher) { _bench_own(bencher, vec![(); 1024]); }

#[bench] fn u64_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![0u64; 1024]); }
#[bench] fn u64_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![0u64; 1024]); }
#[bench] fn u64_own(bencher: &mut Bencher) { _bench_own(bencher, vec![0u64; 1024]); }

#[bench] fn u8_u64_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn u8_u64_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn u8_u64_own(bencher: &mut Bencher) { _bench_own(bencher, vec![(0u8, 0u64); 512]); }

#[bench] fn string10_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string10_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string10_own(bencher: &mut Bencher) { _bench_own(bencher, vec![format!("grawwwwrr!"); 1024]); }

#[bench] fn string20_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn string20_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn string20_own(bencher: &mut Bencher) { _bench_own(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }

#[bench] fn vec_u_s_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_s_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_s_own(bencher: &mut Bencher) { _bench_own(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[bench] fn vec_u_vn_s_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_vn_s_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_vn_s_own(bencher: &mut Bencher) { _bench_own(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }

fn _bench_enc<T: Abomonation>(bencher: &mut Bencher, record: T) {

    // prepare encoded data for bencher.bytes
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);

    // repeatedly encode this many bytes
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        bytes.clear();
        encode(&record, &mut bytes);
    });
}

fn _bench_dec<T: Abomonation+Eq>(bencher: &mut Bencher, record: T) {

    // prepare encoded data
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        decode::<T>(&mut bytes).is_some()
        // assert!(&record == result);
    });
}

fn _bench_own<T: Abomonation+Eq+Clone>(bencher: &mut Bencher, record: T) {

    // prepare encoded data
    let mut bytes = Vec::new();
    encode(&record, &mut bytes);

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        (*decode::<T>(&mut bytes[..]).unwrap().0).clone()
        // assert!(record == result);
    });
}
