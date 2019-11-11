#![feature(test)]

extern crate abomonation;
extern crate test;

use abomonation::*;
use test::Bencher;

#[bench] fn empty_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![(); 1024]); }
#[bench] fn empty_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![(); 1024]); }

#[bench] fn u64_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![0u64; 1024]); }
#[bench] fn u64_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![0u64; 1024]); }

#[bench] fn u8_u64_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![(0u8, 0u64); 512]); }
#[bench] fn u8_u64_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![(0u8, 0u64); 512]); }

#[bench] fn string10_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![format!("grawwwwrr!"); 1024]); }
#[bench] fn string10_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![format!("grawwwwrr!"); 1024]); }

#[bench] fn string20_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }
#[bench] fn string20_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![format!("grawwwwrr!!!!!!!!!!!"); 512]); }

#[bench] fn vec_u_s_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_s_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![vec![(0u64, format!("grawwwwrr!")); 32]; 32]); }

#[bench] fn vec_u_vn_s_e_d(bencher: &mut Bencher) { _bench_e_d(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }
#[bench] fn vec_u_vn_s_cln(bencher: &mut Bencher) { _bench_cln(bencher, vec![vec![(0u64, vec![(); 1 << 40], format!("grawwwwrr!")); 32]; 32]); }

fn _bench_e_d<T>(bencher: &mut Bencher, record: T)
    where for<'de> T: Abomonation<'de>
{
    // prepare encoded data for bencher.bytes
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // repeatedly encode this many bytes
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        bytes = vec![];
        unsafe { encode(&record, &mut bytes).unwrap(); }
        unsafe { decode::<T>(&mut bytes) }.is_some()
    });
}

fn _bench_cln<T>(bencher: &mut Bencher, record: T)
    where for<'de> T: Abomonation<'de> + Clone
{
    // prepare encoded data
    let mut bytes = Vec::new();
    unsafe { encode(&record, &mut bytes).unwrap(); }

    // repeatedly decode (and validate)
    bencher.bytes = bytes.len() as u64;
    bencher.iter(|| {
        record.clone()
    });
}
