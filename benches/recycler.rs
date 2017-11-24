#![feature(test)]

extern crate recycler;
extern crate abomonation;
extern crate test;

use recycler::{Recyclable, Recycler, make_recycler};
use abomonation::*;
use test::Bencher;
// use std::io::Read;

#[bench] fn empty_own(bencher: &mut Bencher) { _bench_own(bencher, vec![(); 1024]); }
#[bench] fn u64_own(bencher: &mut Bencher) { _bench_own(bencher, vec![0u64; 1024]); }
#[bench] fn u8_u64_own(bencher: &mut Bencher) { _bench_own(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn string10_own(bencher: &mut Bencher) { _bench_own(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string20_own(bencher: &mut Bencher) { _bench_own(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn vec_u_s_own(bencher: &mut Bencher) { _bench_own(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_vn_s_own(bencher: &mut Bencher) { _bench_own(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }

#[bench] fn empty_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![(); 1024]); }
#[bench] fn u64_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![0u64; 1024]); }
#[bench] fn u8_u64_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn string10_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string20_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn vec_u_s_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

// TODO : this reveals that working with a `vec![(); 1 << 40]` does not get optimized away.
// #[bench] fn vec_u_vn_s_rec(bencher: &mut Bencher) { _bench_rec(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }

fn _bench_own<T: Abomonation+Clone>(bencher: &mut Bencher, record: T) {

    // prepare encoded data
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        (*unsafe {decode::<T>(&mut bytes[..]) }.unwrap().0).clone()
        // assert!(record == result);
    });
}


fn _bench_rec<T: Abomonation+Recyclable>(bencher: &mut Bencher, record: T) {

    // prepare encoded data
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }
    let mut recycler = make_recycler::<T>();
    recycler.recycle(record);

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        let result = recycler.recreate(unsafe { decode::<T>(&mut bytes[..]) }.unwrap().0);
        recycler.recycle(result);
    });
}
