/// Tools for storing abomonated objects with correct alignment
///
/// Use of `decode::<T>()` requires that the input bytes are aligned on a
/// `T::alignment()` boundary, or else undefined behavior will ensue.
///
/// This module provides tools for ensuring this alignment constraint on input
/// bytes of unknown or known-incorrect alignment before calling `decode()`.

use crate::{
    Entomb,
    Exhume,
};

use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};


/// Overaligned `Box<[u8]>` for abomonated objects of type T
///
/// Compared with a regular `Box<[u8]>`, this heap-allocated bag of bytes also
/// ensures that the heap allocation is aligned on `T::alignment()`, and thus
/// suitable for use as input to `decode::<T>()`.
pub struct Coffin<T: Entomb>(NonNull<[u8]>, PhantomData<T>);

impl<T: Entomb> Coffin<T> {
    /// Copy abomonated bytes into a suitably aligned heap allocation
    ///
    /// May abort the computation if memory is exhausted or the system allocator
    /// is not able to satisfy the size or alignment requirements.
    pub fn new(bytes: &[u8]) -> Self {
        // Compute the memory layout of the target memory allocation
        let size = bytes.len();
        let layout = Self::layout(size);

        // Handle zero-sized types just like Box does
        if layout.size() == 0 {
            return Self (
                unsafe { std::slice::from_raw_parts_mut(
                    NonNull::dangling().as_ptr(),
                    0,
                ) }.into(),
                PhantomData,
            )
        }

        // Perform the memory allocation using the system allocator. This is
        // safe because all safety preconditions are checked by Self::layout(),
        // except for zero-sized allocations which we checked above.
        let ptr = unsafe { alloc::alloc(layout) };

        // Abort on memory allocation errors the recommended way. Since the
        // system allocator may abort, no point in not aborting ourselves...
        if ptr.is_null() { alloc::handle_alloc_error(layout); }

        // Transfer the input bytes on our new allocation. This is safe as...
        // - `bytes.as_ptr()` has to be valid for `size` by slice construction
        // - `ptr` is non-null and must point to a memory region of `size` bytes
        // - Pointers are always byte-aligned, so alignment is irrelevant.
        // - Heap allocations may not overlap with existing objects.
        unsafe { ptr.copy_from_nonoverlapping(bytes.as_ptr(), size); }

        // Produce the output slice. The transmute is safe as...
        // - We don't care about lifetimes as we want a NonNull in the end
        // - As discussed above, `ptr` is non-null and well-aligned.
        // - The bytes of the slice have been initialized above
        Self(unsafe { std::slice::from_raw_parts_mut(ptr, size) }.into(),
             PhantomData)
    }

    /// Compute the proper layout for a coffin allocation, checking most safety
    /// preconditions of the system memory allocator along the way **except for
    /// the "no zero-sized allocation" requirement**.
    ///
    /// We handle errors via panics because they all emerge from edge cases that
    /// should only be encountered by users actively trying to break this code.
    fn layout(size: usize) -> Layout {
        // Basic sanity check for debug builds
        debug_assert!(size >= std::mem::size_of::<T>(),
                      "Requested size is quite obviously not big enough");

        // At this point, the only layout errors that remain are those caused by
        // a bad Abomonation::alignment implementation (alignment is zero or not
        // a power of 2) or by a huge input size (close to usize::MAX).
        Layout::from_size_align(size, T::alignment())
               .expect("Bad Abomonation::alignment() impl or excessive size")
    }
}

impl<T: Entomb> Deref for Coffin<T> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        // This is safe as...
        // - The target allocation is live until the Coffin will be dropped.
        // - Normal borrow-checking rules apply and prevent the user from
        //   aliasing or retaining the output reference in an invalid way.
        //
        // ...but see the Drop documentation for a possible edge case :(
        unsafe { self.0.as_ref() }
    }
}

impl<T: Entomb> DerefMut for Coffin<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // This is safe for the same reason that Deref is.
        unsafe { self.0.as_mut() }
    }
}

impl<T: Entomb> Drop for Coffin<T> {
    fn drop(&mut self) {
        // In principle, this should be safe for the same reason that DerefMut
        // is, however there is a wrinkle for all of those...
        //
        // If we want any form of Deref to be safe, the Rust compiler must
        // prevent LLVM from inserting memory reads from the slice after
        // deallocation, and currently it doesn't.
        //
        // There is no clear reason why LLVM would do this, though, and `std`
        // encounters the same problem everywhere, so we'll take the risk...
        //
        // FIXME: Once the Rust team has figured out the right way to handle
        //        this, use it here if it requires manual action.
        //
        //        Here's one ongoing discussion of this topic for reference:
        //        https://github.com/rust-lang/rust/issues/55005
        let slice = unsafe { self.0.as_mut() };

        // There is no allocation to deallocate for zero-sized types.
        if slice.len() == 0 {
            return;
        }

        // Deallocate the memory otherwise. This is safe because...
        // - Every Coffin is always created with its own allocation, only Drop
        //   can liberate it, and Drop will only be called once.
        // - Layout is computed in the same way as in `Coffin::new()`, and the
        //   size of the target slice is the same as that of new's input bytes.
        unsafe { alloc::dealloc(slice.as_mut_ptr(),
                                Self::layout(slice.len())); }
    }
}


/// `Cow`-style abstraction for aligning abomonated bytes before `decode()`
///
/// Often, one needs to decode input bytes which are _probably_ well-aligned,
/// but may not always to be. For example, POSIX memory allocations are aligned
/// on 16-byte boundaries, which is sufficient for most types... as long as
/// multiple abomonated objects are not stored in a sequence without padding
/// bytes in between.
///
/// In those circumstances, pessimistically using `Coffin<T>` all the time
/// would cause unnecessarily intensive use of the system memory allocator.
/// Instead, it is better to check if the input bytes are well-aligned and only
/// reallocate them if necessary, which is what this abstraction does.
pub enum AlignedBytes<'bytes, T: Exhume<'bytes>> {
    /// The orignal bytes were sufficiently well-aligned
    Borrowed(&'bytes mut [u8]),

    /// The abomonated bytes were relocated into a well-aligned heap location
    Owned(Coffin<T>),
}

impl<'bytes, T: Exhume<'bytes>> AlignedBytes<'bytes, T> {
    /// Prepare possibly misaligned bytes for decoding
    pub fn new(bytes: &'bytes mut [u8]) -> Self {
        let misalignment = (bytes.as_ptr() as usize) % T::alignment();
        if misalignment == 0 {
            Self::Borrowed(bytes)
        } else {
            Self::Owned(Coffin::new(bytes))
        }
    }
}

impl<'bytes, T: Exhume<'bytes>> From<&'bytes mut [u8]> for AlignedBytes<'bytes, T> {
    fn from(bytes: &'bytes mut [u8]) -> Self {
        Self::new(bytes)
    }
}

impl<'bytes, T: Exhume<'bytes>> From<Coffin<T>> for AlignedBytes<'bytes, T> {
    fn from(coffin: Coffin<T>) -> Self {
        Self::Owned(coffin)
    }
}

impl<'bytes, T: Exhume<'bytes>> Deref for AlignedBytes<'bytes, T> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(o) => o,
        }
    }
}

impl<'bytes, T: Exhume<'bytes>> DerefMut for AlignedBytes<'bytes, T> {
    fn deref_mut(&mut self) -> &mut [u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(o) => o,
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{AlignedBytes, Coffin, Entomb, Exhume};

    #[test]
    fn coffin() {
        check_coffin::<u8>();
        check_coffin::<u16>();
        check_coffin::<u32>();
        check_coffin::<u64>();
        check_coffin::<u128>();
    }

    fn check_coffin<T: Entomb>() {
        let bytes = make_test_bytes_for::<T>();
        let coffin = Coffin::<T>::new(&bytes[..]);
        assert_eq!(&coffin[..], &bytes[..],
                   "Coffin data is incorrect");
        assert_eq!(coffin.as_ptr() as usize % T::alignment(), 0,
                   "Coffin alignment is not strong enough");
    }

    #[test]
    fn aligned_bytes() {
        check_aligned_bytes::<u16>();
        check_aligned_bytes::<u32>();
        check_aligned_bytes::<u64>();
        check_aligned_bytes::<u128>();
    }

    fn check_aligned_bytes<T>()
        where for<'a> T: Exhume<'a>
    {
        assert!(std::mem::align_of::<T>() > 1,
                "This test requires generating misaligned data");

        let mut bytes = make_test_bytes_for::<T>();
        let mut coffin = Coffin::<T>::new(&bytes[..]);
        let aligned_bytes = AlignedBytes::<T>::new(&mut coffin[..]);
        match aligned_bytes {
            AlignedBytes::Borrowed(_) => {}
            AlignedBytes::Owned(_) => panic!("Should not allocate here"),
        }
        assert_eq!(&aligned_bytes[..], &bytes[..]);

        bytes.push(42);
        let mut coffin = Coffin::<T>::new(&bytes[..]);
        let aligned_bytes = AlignedBytes::<T>::new(&mut coffin[1..]);
        match aligned_bytes {
            AlignedBytes::Borrowed(_) => panic!("Should allocate here"),
            AlignedBytes::Owned(_) => {},
        }
        assert_eq!(&aligned_bytes[..], &bytes[1..]);
    }

    fn make_test_bytes_for<T>() -> Vec<u8> {
        let mut i = 0;
        std::iter::repeat_with(|| { i += 1; i })
                  .take(std::mem::size_of::<T>())
                  .collect::<Vec<_>>()
    }
}
