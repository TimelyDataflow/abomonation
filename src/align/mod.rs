/// Utilities for handling alignment in abomonated data

mod io;
mod alloc;

#[deprecated(note = "Made pub for internal unsafe_abomonate use only")]
pub use self::io::{AlignedReader, AlignedWriter};

pub use self::alloc::{AlignedBytes, Coffin};
