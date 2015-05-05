//! Abomonation (spelling intentional) is a fast serialization / deserialization crate.
//!
//! Abomonation takes vectors of types and simply writes their contents as binary.
//! It then gives each typed element of the vector the opportunity to serialize more data, which is
//! useful for types with owned memory such as String and Vec.
//! The result is effectively a copy of reachable memory, where pointers are zero-ed out and vector
//! capacities are set to the vector length. The intended locations of pointers can be recovered on
//! deserialization by consuming binary data in the same way it was produced.
//!
//! Abomonation does several unsafe things, and should ideally be used only through the methods
//! `encode` and `decode` on types implementing the `Abomonation` trait.
//! Implementing the `Abomonation` trait is highly discouraged, unless you are just doing a
//! copy/paste of the tuple code for your struct.
//!
//! **Very important**: Abomonation reproduces the memory as laid out by the serializer, and this means
//! architectural variations are revealed. Data encoded on a 32bit big-endian machine will not
//! decode properly on a 64bit little-endian machine. Ideally it won't eat your laundry, but rather panic.
//!
//!
//! #Examples
//! ```
//! use abomonation::{encode, decode};
//!
//! // create some test data out of abomonation-approved types
//! let vector = (0..256u64).map(|i| (i, format!("{}", i))).collect();
//!
//! // encode vector into a Vec<u8>
//! let mut bytes = Vec::new();
//! encode(&vector, &mut bytes);
//!
//! // decode a &Vec<(u64, String)> from binary data
//! if let Ok(result) = decode::<(u64, String)>(&mut bytes) {
//!     assert!(result == &vector);
//! }
//! ```

// extern crate num;

use std::mem;       // yup, used pretty much everywhere.
use std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.
// use std::traits::PrimInt;

/// Encodes a vector of typed data into a binary buffer.
///
/// `encode` will transmute `typed` to binary and write its contents to `bytes`. After doing this,
/// it will offer each element of typed the opportunity to serialize more data. Having done that,
/// it offers each element the opportunity to "tidy up", in which the elements can erasing things
/// like memory addresses that it is impolite to share.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i))).collect();
///
/// // encode vector into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from binary data
/// if let Ok(result) = decode::<(u64, String)>(&mut bytes) {
///     assert!(result == &vector);
/// }
/// ```
///
pub fn encode<T: Abomonation>(typed: &Vec<T>, bytes: &mut Vec<u8>) {
    let slice = unsafe { std::slice::from_raw_parts(mem::transmute(typed), mem::size_of::<Vec<T>>()) };
    bytes.write_all(slice).unwrap();    // write to a Vec<u8> is claimed to never fail.
    let result: &mut Vec<T> = unsafe { mem::transmute(bytes.get_unchecked_mut(0)) };
    unsafe { result.embalm(); }
    unsafe { typed.entomb(bytes); }
}

/// Decodes a binary buffer into a reference to a typed vector.
///
/// `decode` will read a `Vec<T>` amount of data from the head of `bytes`, and then use the length
/// there to read enough additional data from `bytes` to back its memory. It then proceeds to `exhume`
/// each element, offering them the ability to consume prefixes of `bytes` to back further owned data.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i))).collect();
///
/// // encode vector into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from binary data
/// if let Ok(result) = decode::<(u64, String)>(&mut bytes) {
///     assert!(result == &vector);
/// }
/// ```
pub fn decode<T: Abomonation>(bytes: &mut [u8]) -> Result<&Vec<T>,&mut [u8]> {
    let (split1, split2) = bytes.split_at_mut(mem::size_of::<Vec<T>>());

    let result: &mut Vec<T> = unsafe { mem::transmute(split1.get_unchecked_mut(0)) };
    unsafe { try!(result.exhume(split2)); }
    Ok(result)
}

/// Abomonation provides methods to serialize any heap data the implementor owns.
///
/// The default implementations for Abomonation's methods are all empty. The majority of types have
/// no owned data to transcribe. Some do, however, and need to carefully implement these unsafe methods.
///
/// #Safety
///
/// Abomonation has no safe methods. Please do not call them. They are intended to be called only by
/// `encode` and `decode`, each of which impose restrictions on ownership and lifetime of the data
/// they take as input and return as output.
pub trait Abomonation {

    /// Write any additional information about `&self` beyond its binary representation.
    ///
    /// Most commonly this is owned data on the other end of pointers in `&self`.
    unsafe fn entomb(&self, _writer: &mut Vec<u8>) { }

    /// Perform any final edits before committing `&mut self`.
    ///
    /// Most commonly this overwrites pointers whose values should not be recorded.
    unsafe fn embalm(&mut self) { }

    /// Recover any information for `&mut self` not evident from its binary representation.
    ///
    /// Most commonly this populates pointers with valid references into `_bytes`.
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> { Ok(bytes) }
}

impl Abomonation for u8 { }
impl Abomonation for u64 {
    // TODO : if these were optimized out, hooray! they aren't.
    // unsafe fn embalm(&mut self) { *self = (*self).to_le(); }
    // unsafe fn exhume(&mut self, bytes: &mut &[u8]) -> Result<(), ()> { *self = u64::from_le(*self); Ok(()) }
}
impl<T1: Abomonation, T2: Abomonation> Abomonation for (T1, T2) {
    unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); }
    unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Result<&'b mut [u8],&'b mut [u8]> {
        let tmp = bytes;
        bytes = try!(self.0.exhume(tmp));
        let tmp = bytes;
        bytes = try!(self.1.exhume(tmp));
        Ok(bytes)
    }
}

impl Abomonation for String {
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, String::from_raw_parts(0 as *mut u8, self.len(), self.len()));
    }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        bytes.write_all(self.as_bytes()).unwrap();
    }
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8],&'b mut [u8]> {
        if self.len() > bytes.len() { Err(bytes) }
        else {
            let (mine, rest) = bytes.split_at_mut(self.len());
            std::ptr::write(self, String::from_raw_parts(mem::transmute(mine.as_ptr()), self.len(), self.len()));
            Ok(rest)
        }
    }
}

impl<T: Abomonation> Abomonation for Vec<T> {
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, Vec::from_raw_parts(0 as *mut T, self.len(), self.len()));
    }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        let position = bytes.len();
        bytes.write_all(typed_to_bytes(&self[..])).unwrap();
        for element in bytes_to_typed::<T>(&mut bytes[position..]) { element.embalm(); }
        for element in self.iter() { element.entomb(bytes); }
    }
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8],&'b mut [u8]> {

        // extract memory from bytes to back our vector
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { Err(bytes) }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);

            // transmute back to &mut [u8], and then transmute to &mut [T].
            let slice: &mut [T] = bytes_to_typed(mem::transmute(mine));

            // build a new vector using this memory
            let vector = Vec::from_raw_parts(slice.as_mut_ptr(), self.len(), self.len());

            // overwrite *self w/o dropping it.
            std::ptr::write(self, vector);

            // pretend everything is normal; call exhume on each element
            for element in self.iter_mut() {
                let temp = rest;
                rest = try!(element.exhume(temp));
            }
            Ok(rest)
        }
    }
}


unsafe fn typed_to_bytes<T>(slice: &[T]) -> &[u8] {
    std::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * mem::size_of::<T>())
}

unsafe fn bytes_to_typed<T>(slice: &mut [u8]) -> &mut [T] {
    std::slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut T, slice.len() / mem::size_of::<T>())
}
