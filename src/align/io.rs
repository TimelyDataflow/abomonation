/// Tools for reading and writing abomonated data in an alignment-aware way
///
/// In order to enable UB-free in-place deserialization, abomonated objects
/// follow Rust's normal memory alignment rules. This requires inserting padding
/// bytes between serialized data and skipping them on readout. This module
/// provides tools to take care of this.

use std::{
    io::Write,
    mem,
    ptr::NonNull,
};


/// Alignment-aware binary data writer
///
/// This wrapper around a standard Rust writer allows writing multiple binary
/// objects in a sequence with a memory layout that is suitable for in-place
/// readout. It does so by inserting padding bytes between the objects as if
/// they were members of a well-aligned C-style struct whose alignment is the
/// maximum of the alignment of all written objects.
pub struct AlignedWriter<W: Write> {
    /// Inner writer to which data is eventually dispatched
    inner: W,

    /// Amount of data that was sent to the inner writer so far
    written_so_far: usize,

    /// Expected alignment of the output data
    #[cfg(debug_assertions)]
    output_alignment: usize,
}

impl<W: Write> AlignedWriter<W> {
    /// Prepare a writer for alignment-aware binary writes
    ///
    /// In debug builds, `AlignedWriter` will check that the output memory
    /// allocation is sufficiently well-aligned for the data that is written
    /// into it, as per the `output_alignment` parameter to this function.
    //
    // FIXME: output_alignment should be #[cfg(debug_assertions)], but at the
    //        moment Rust 1.39 is a bit too freshly released to rely on that.
    #[allow(unused)]
    pub fn new(inner: W, output_alignment: usize) -> Self {
        Self {
            inner,
            written_so_far: 0,
            #[cfg(debug_assertions)] output_alignment,
        }
    }

    /// Write arbitrary binary data into the inner writer
    ///
    /// This is unsafe because Rust does not yet provide an UB-free way to
    /// expose the padding bytes of arbitrary T objects to writers.
    pub unsafe fn write_slice<T>(&mut self, data: &[T]) -> crate::IOResult<()> {
        // Check how aligned the binary data needs to be
        let alignment = mem::align_of_val::<[T]>(data);

        // In debug builds, check that the output allocation has sufficiently
        // strong alignment for the data that's being written to it.
        //
        // If the output alignment is too low, readout may go wrong because the
        // AlignedReader will skip a number of padding bytes that may not be
        // in sync with the amount that AlignedWriter has inserted, in a manner
        // that depends on how the data being read out was _actually_ aligned.
        debug_assert!(
            if cfg!(debug_assertions) { alignment <= self.output_alignment } else { true },
            "Insufficient output alignment (output alignment is {}, got data of alignment {})",
            self.output_alignment, alignment
        );

        // Inject padding bytes until the output is well-aligned, assuming that
        // the first byte that was written was well-aligned for all output data.
        while self.written_so_far % alignment != 0 {
            self.inner.write_all(&[0u8])?;
            self.written_so_far += 1;
        }

        // Write down the binary data and exit
        // FIXME: Move write_bytes functionality here
        crate::write_bytes(&mut self.inner, data)?;
        self.written_so_far += mem::size_of_val::<[T]>(data);
        Ok(())
    }

    /// Convenience function for non-slice data
    ///
    /// This is unsafe for the same reason that `write_slice` is.
    pub unsafe fn write<T>(&mut self, data: &T) -> crate::IOResult<()> {
        self.write_slice(std::slice::from_ref(data))
    }

    /// Query how much data was written so far
    pub fn written_so_far(&self) -> usize {
        self.written_so_far
    }
}

impl<W: Write> Write for AlignedWriter<W> {
    fn write(&mut self, buf: &[u8]) -> crate::IOResult<usize> {
        // This will write buf.len() data because bytes are always well-aligned
        // It is safe because &[u8] has no padding bytes
        unsafe { self.write_slice(buf)? };
        Ok(buf.len())
    }

    fn flush(&mut self) -> crate::IOResult<()> {
        // No flushing necessary, we don't buffer anything
        Ok(())
    }
}


/// Slice-of-bytes reader for data written by `AlignedWriter`
///
/// This reader takes as input a bunch of bytes that were written by
/// `AlignedWriter` and allows fetching back the corresponding binary data under
/// the assumption that the input bytes are aligned on the max of the alignment
/// of all the data that was written by `AlignedWriter`.
pub struct AlignedReader<'bytes> {
    /// Remaining bytes to be read
    bytes: &'bytes mut [u8],

    /// Expected alignment of the input data
    #[cfg(debug_assertions)]
    input_alignment: usize,
}

impl<'bytes> AlignedReader<'bytes> {
    /// Prepare some bytes for alignment-aware readout
    ///
    /// In debug builds, `AlignedReader` will check that the input bytes were
    /// sufficiently well-aligned for the data that is being read from it, as
    /// per the `input_alignment` parameter to this function.
    //
    // FIXME: input_alignment should be #[cfg(debug_assertions)], but at the
    //        moment Rust 1.39 is a bit too freshly released to rely on that.
    #[allow(unused)]
    pub fn new(bytes: &'bytes mut [u8], input_alignment: usize) -> Self {
        debug_assert_eq!((bytes.as_ptr() as usize) % input_alignment, 0,
                         "Input data is not aligned on a {}-byte boundary as expected",
                         input_alignment);
        Self {
            bytes,
            #[cfg(debug_assertions)] input_alignment,
        }
    }

    /// Read a slice of data of arbitrary type from the inner bytes, returns a
    /// pointer to the first element of the slice, or None if the request
    /// overflows the input bytes.
    //
    // FIXME: This should return a NonNull<[T]>, but pointers to slices are not
    //        ergonomic enough at this point in time.
    pub fn read_slice<T>(&mut self, len: usize) -> Option<NonNull<T>> {
        // As far as I know, zero-length slices may be aligned differently but
        // all nonzero-length slices are aligned identically
        let alignment = if len == 0 {
            mem::align_of::<[T; 0]>()
        } else {
            mem::align_of::<[T; 1]>()
        };

        // In debug builds, check that the input allocation has sufficiently
        // strong alignment for the data that's being read from it.
        //
        // If the input alignment is too low, readout may go wrong because the
        // AlignedReader will skip a number of padding bytes that may not be
        // in sync with the amount that AlignedWriter has inserted, in a manner
        // that depends on how the data being read out was _actually_ aligned.
        debug_assert!(
            if cfg!(debug_assertions) { alignment <= self.input_alignment } else { true },
            "Insufficient input alignment (input alignment is {}, asked for data of alignment {})",
            self.input_alignment, alignment
        );

        // Drop the alignment padding bytes leading up to the inner T-typed data
        let misalignment = self.bytes.as_ptr() as usize % alignment;
        if misalignment != 0 {
            let offset = alignment - misalignment;
            if offset > self.bytes.len() { return None; }
            // In an ideal world, one could just write:
            //     self.bytes = &mut self.bytes[offset..]
            // Alas, in this world, we need...
            self.bytes = unsafe {
                mem::transmute::<&mut [u8], &'bytes mut [u8]>(&mut self.bytes[offset..])
            };
        }

        // Make sure that we sill have enough bytes for readout
        let size = mem::size_of::<T>() * len;
        if size > self.bytes.len() { return None; }

        // Extract the inner T-typed data
        // This is safe because we checked that the input size is large enough
        // and the first pointer of a slice cannot be null
        let (out, rest) = self.bytes.split_at_mut(size);
        let result: NonNull<T> = unsafe {
            NonNull::new_unchecked(out.as_mut_ptr() as *mut T)
        };

        // Update the inner slice. In an ideal world, one could just write
        //     self.bytes = rest
        // Alas, in this world, we need...
        self.bytes = unsafe {
            mem::transmute::<&mut [u8], &'bytes mut [u8]>(rest)
        };
        Some(result)
    }

    /// Read arbitrary data from the inner bytes
    pub fn read<T>(&mut self) -> Option<NonNull<T>> {
        self.read_slice(1)
    }

    /// Extract the remaining bytes
    pub fn remaining(self) -> &'bytes mut [u8] {
        self.bytes
    }
}


#[cfg(test)]
mod tests {
    use crate::align::AlignedBytes;
    use super::{AlignedReader, AlignedWriter};

    #[test]
    fn round_trip() {
        // We'll write the following binary data down
        let u1 = 0x42u8;
        let u2 = 0x12345678_9abcdef0_u64;
        let u3s = [0x13579bdf_u32, 0x2468ace0_u32];
        type UMax = u64;
        let max_align = std::mem::align_of::<UMax>();

        // Build a writer for it
        let mut bytes = Vec::new();
        let mut writer = AlignedWriter::new(&mut bytes, max_align);

        // Write it down
        unsafe {
            writer.write(&u1).unwrap();
            writer.write(&u2).unwrap();
            writer.write_slice(&u3s[..]).unwrap();
        }

        // Check written bytes counter
        let written = writer.written_so_far();
        std::mem::drop(writer);
        assert_eq!(written, bytes.len(),
                   "Number of reported written bytes is wrong");
        assert_eq!(written, 1 + 7 + 8 + 4 + 4,
                   "Reported written bytes does not match written data");

        // Check written data
        assert_eq!(bytes[0], u1,
                   "8-bit number was written wrong");
        assert_eq!(bytes[1..8], [0, 0, 0, 0, 0, 0, 0],
                   "Padding for 64-bit number was written wrong");
        assert_eq!(bytes[8..16], u2.to_ne_bytes(),
                   "64-bit number was written wrong");
        assert_eq!(bytes[16..20], u3s[0].to_ne_bytes(),
                   "First 32-bit number was written wrong");
        assert_eq!(bytes[20..24], u3s[1].to_ne_bytes(),
                   "Second 32-bit number was written wrong");

        // Prepare to read back the data
        let mut aligned_bytes = AlignedBytes::<UMax>::new(&mut bytes[..]);
        let mut reader = AlignedReader::new(&mut aligned_bytes, max_align);

        // Read back the data
        unsafe {
            assert_eq!(reader.read::<u8>().unwrap().as_ref(), &u1,
                       "8-bit number was read wrong");
            assert_eq!(reader.read::<u64>().unwrap().as_ref(), &u2,
                       "64-bit number was read wrong");
            let slice_ptr = reader.read_slice::<u32>(u3s.len()).unwrap();
            let slice = std::slice::from_raw_parts(slice_ptr.as_ptr(),
                                                   u3s.len());
            assert_eq!(slice, &u3s,
                       "32-bit numbers were read wrong");
        }

        // Make sure that we consumed all the bytes
        assert_eq!(reader.remaining(), &[],
                   "No bytes should remain");
    }
}
