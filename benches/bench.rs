#![feature(test)]

extern crate abomonation;
extern crate test;

use abomonation::*;
use test::Bencher;

#[bench] fn empty_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![(); 1024]); }
#[bench] fn empty_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![(); 1024]); }

#[bench] fn u64_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![0u64; 1024]); }
#[bench] fn u64_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![0u64; 1024]); }

#[bench] fn u32x2_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![(0u32,0u32); 1024]); }
#[bench] fn u32x2_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![(0u32,0u32); 1024]); }

#[bench] fn u8_u64_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn u8_u64_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![(0u8, 0u64); 512]); }

#[bench] fn string10_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string10_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![format!("grawwwwrr!"); 1024]); }

#[bench] fn string20_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn string20_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }

#[bench] fn vec_u_s_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_s_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[bench] fn vec_u_vn_s_enc(bencher: &mut Bencher) { _bench_enc(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_vn_s_dec(bencher: &mut Bencher) { _bench_dec(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }

fn _bench_enc<T: Abomonation>(bencher: &mut Bencher, record: T) {
    // prepare encoded data for bencher.bytes
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // repeatedly encode this many bytes
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        bytes.clear();
        unsafe { encode(&record, &mut bytes).unwrap() }
    });
}

fn _bench_dec<T: Abomonation+Eq>(bencher: &mut Bencher, record: T) {
    // prepare encoded data
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        unsafe { decode::<T>(&mut bytes) }.is_some()
        // assert!(&record == result);
    });
}
