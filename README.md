# Abomonation
A mortifying serialization library for Rust

Abomonation (spelling intentional) is a serialization library for Rust based on the very simple idea that if someone presents data for serialization it will copy those exact bits, and then follow any pointers and copy those bits, and so on. When deserializing it recovers the exact bits, and then corrects pointers to aim at the serialized forms of the chased data.

**Warning**: Abomonation should not be used on any data you care strongly about, or from any computer you value the data on. The `encode` and `decode` methods do things that are currently undefined behavior, and you shouldn't stand for that.

Please consult the [abomonation documentation]( "https://frankmcsherry.github.com/abomonation") for more specific information.

Here is an example of using Abomonation. It is very easy to use. Frighteningly easy.

```rust
extern crate abomonation;
use abomonation::{encode, decode};

// create some test data out of abomonation-approved types
let vector = (0..256u64).map(|i| (i, format!("{}", i))).collect();

// encode vector into a Vec<u8>
let mut bytes = Vec::new();
encode(&vector, &mut bytes);

// decode a &Vec<(u64, String)> from binary data
if let Ok((result, remaining) = decode::<Vec<(u64, String)>>(&mut bytes) {
    assert!(result == &vector);
    assert!(remaining.len() == 0);
}
```

When you use Abomonation things may go really fast. That is because it does so little work, and mostly just copies large hunks of memory. Typing

    cargo bench

will trigger Rust's benchmarking infrastructure (or an error if you are not using nightly. bad luck). The tests repeatedly encode `Vec<u64>`, `Vec<String>`, and `Vec<Vec<(u64, String)>>` giving numbers like:

    test u64_enc        ... bench:         131 ns/iter (+/- 58) = 62717 MB/s
    test string10_enc   ... bench:       8,784 ns/iter (+/- 2,791) = 3966 MB/s
    test vec_u_s_enc    ... bench:       8,964 ns/iter (+/- 1,439) = 4886 MB/s

They also repeatedly decode the same data, giving numbers like:

    test u64_dec        ... bench:           2 ns/iter (+/- 1) = 4108000 MB/s
    test string10_dec   ... bench:       1,058 ns/iter (+/- 349) = 32930 MB/s
    test vec_u_s_dec    ... bench:       1,232 ns/iter (+/- 223) = 35551 MB/s

These throughputs are so high because there is very little to do: internal pointers need to be corrected, but in their absence (*e.g.* `u64`) there is literally nothing to do.

Be warned that these numbers are not *goodput*, but rather the total number of bytes moved, which is equal to the in-memory representation of the data. On a 64bit system, a `String` requires 24 bytes plus one byte per character, which can be a lot of overhead for small strings.

## unsafe_abomonate!

Abomonation comes with the `unsafe_abomonate!` macro implementing `Abomonation` for structs which are essentially equivalent to a tuple of other `Abomonable` types. To use the macro, you must put the `#[macro_use]` modifier before `extern crate abomonation;`.

Please note that `unsafe_abomonate!` synthesizes unsafe implementations of `Abomonation`, and it is should be considered unsafe to invoke.

```rust
#[macro_use]
extern crate abomonation;
use abomonation::{encode, decode};

#[derive(Eq, PartialEq)]
struct MyStruct {
    pub a: String,
    pub b: u64,
    pub c: Vec<u8>,
}

// (type : field1, field2 .. )
unsafe_abomonate!(MyStruct : a, b, c);

// create some test data out of abomonation-approved types
let record = MyStruct{ a: "test".to_owned(), b: 0, c: vec![0, 1, 2] };

// encode vector into a Vec<u8>
let mut bytes = Vec::new();
encode(&record, &mut bytes);

// decode a &Vec<(u64, String)> from binary data
if let Ok((result, remaining)) = decode::<MyStruct>(&mut bytes) {
    assert!(result == &record);
    assert!(remaining.len() == 0);
}
```

Be warned that implementing `Abomonable` for types can be a giant disaster and is entirely discouraged.
