/// Utilities for handling alignment in abomonated data

mod io;

#[deprecated(note = "Made pub for internal unsafe_abomonate use only")]
pub use self::io::{AlignedReader, AlignedWriter};
