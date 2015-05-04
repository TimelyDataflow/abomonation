# Abomonation
A mortifying serialization library for Rust

Abomonation (spelling intentional) is a serialization library for Rust based on the very simple idea that if someone presents data for serialization it will copy those exact bits, and then follow any pointers and copy those bits. When deserializing it recovers the exact bits, and then corrects pointers to aim at the serialized forms of the chased data.

Abomonation should not be used on any data you care strongly about, or from any computer you value the data on. It really isn't that bad, but it isn't clear how bad it actually is just yet.

Here is an example of using Abomonation. It is very easy to use. Seductively easy.

```rust
use abomonation::{encode, decode};

// create some test data out of abomonation-approved types
let vector = (0..256u64).map(|i| (i, format!("{}", i))).collect();

// encode vector into a Vec<u8>
let mut bytes = Vec::new();
encode(&vector, &mut bytes);

// decode a &Vec<(u64, String)> from binary data
let result = decode::<(u64, String)>(&mut bytes);
assert!(result == &vector);
```

When you use Abomonation things may go really fast. That is because it does so little work, and mostly just copies large hunks of memory. Typing

    cargo bench

will trigger Rust's benchmarking infrastructure (or an error if you are using beta. bad luck). The tests repeatedly encode `Vec<u64>`, `Vec<String>`, and `Vec<Vec<(u64, String)>>` giving numbers like:

    test bench_enc_u64     ... bench:       411 ns/iter (+/- 84) = 19990 MB/s
    test bench_enc_string  ... bench:     12039 ns/iter (+/- 3330) = 2893 MB/s
    test bench_enc_vec_u_s ... bench:     12578 ns/iter (+/- 1665) = 3482 MB/s

They also repeatedly decode the same data, giving numbers like:

    test bench_dec_u64     ... bench:       525 ns/iter (+/- 262) = 15649 MB/s
    test bench_dec_string  ... bench:     11289 ns/iter (+/- 2432) = 3086 MB/s
    test bench_dec_vec_u_s ... bench:     12557 ns/iter (+/- 2183) = 3488 MB/s

Be warned that these numbers are not *goodput*, but rather the total number of bytes moved, which is equal to the in-memory representation of the data. On a 64bit system, a `String` requires 24 bytes plus one byte per character, which can be a lot of overhead for small strings. 
