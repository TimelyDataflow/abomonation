//! Abomonation (spelling intentional) is a fast serialization / deserialization crate.
//!
//! Abomonation takes vectors of types and simply writes their contents as binary.
//! It then gives each typed element of the vector the opportunity to serialize more data, which is
//! useful for types with owned memory such as `String` and `Vec`.
//! The result is effectively a copy of reachable memory, where pointers are zero-ed out and vector
//! capacities are set to the vector length.
//! Deserialization results in a shared slice, where internal pointers reference locations in the
//! binary data itself.
//!
//! Abomonation does several unsafe things, and should ideally be used only through the methods
//! `encode` and `decode` on types implementing the `Abomonation` trait.
//! Implementing the `Abomonation` trait is highly discouraged, unless you are just doing a
//! copy/paste of the tuple code for your struct.
//!
//! **Very important**: Abomonation reproduces the memory as laid out by the serializer, which can
//! reveal architectural variations. Data encoded on a 32bit big-endian machine will not decode
//! properly on a 64bit little-endian machine. Moreover, it could result in undefined behavior if
//! the deserialization results in invalid typed data. Please do not do this.
//!
//!
//! #Examples
//! ```
//! use abomonation::{encode, decode};
//!
//! // create some test data out of abomonation-approved types
//! let vector = (0..256u64).map(|i| (i, format!("{}", i)))
//!                         .collect::<Vec<_>>();
//!
//! // encode a Vec<(u64, String)> into a Vec<u8>
//! let mut bytes = Vec::new();
//! encode(&vector, &mut bytes);
//!
//! // decode a &[(u64, String)] from &mut [u8] binary data
//! if let Ok(result) = decode::<Vec<(u64, String)>>(&mut bytes) {
//!     assert!(result == &vector);
//! }
//! ```

use std::mem;       // yup, used pretty much everywhere.
use std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.

/// Encodes a typed element into a binary buffer.
///
/// `encode` will transmute `typed` to binary and write its contents to `bytes`. It then offers the
/// element the opportunity to serialize more data. Having done that,
/// it offers the element the opportunity to "tidy up", in which the element can erasing things
/// like local memory addresses that it would be impolite to share.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Ok(result) = decode::<Vec<(u64, String)>>(&mut bytes) {
///     assert!(result == &vector);
/// }
/// ```
///
pub fn encode<T: Abomonation>(typed: &T, bytes: &mut Vec<u8>) {
    unsafe {
        let slice = std::slice::from_raw_parts(mem::transmute(typed), mem::size_of::<T>());
        bytes.write_all(slice).unwrap();    // Rust claims a write to a Vec<u8> will never fail.
        let result: &mut T = mem::transmute(bytes.get_unchecked_mut(0));
        result.embalm();
        typed.entomb(bytes);
    }
}

/// Encodes a slice of typed data into a binary buffer.
///
/// `encode_slice` will transmute `typed` to binary and write its contents to `bytes`. After this,
/// it will offer each element of typed the opportunity to serialize more data. Having done that,
/// it offers each element the opportunity to "tidy up", in which the elements can erasing things
/// like local memory addresses that it would be impolite to share.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Ok(result) = decode::<Vec<(u64, String)>>(&mut bytes) {
///     assert!(result == &vector);
/// }
/// ```
///
pub fn encode_slice<T: Abomonation>(typed: &[T], bytes: &mut Vec<u8>) {
    unsafe {
        let slice = std::slice::from_raw_parts(mem::transmute(&typed), mem::size_of::<&[T]>());
        bytes.write_all(slice).unwrap();    // Rust claims a write to a Vec<u8> will never fail.
        let result: &mut &[T] = mem::transmute(bytes.get_unchecked_mut(0));
        result.embalm();
        typed.entomb(bytes);
    }
}

/// Decodes a binary buffer into a reference to a typed element.
///
/// `decode` treats the first `mem::size_of::<T>()` bytes as a T, and will then `exhume` the
/// element, offering it the ability to consume prefixes of `bytes` to back any owned data.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Ok(result) = decode::<Vec<(u64, String)>>(&mut bytes) {
///     assert!(result == &vector);
/// }
/// ```
pub fn decode<T: Abomonation>(bytes: &mut [u8]) -> Result<&T, &mut [u8]> {
    if bytes.len() < mem::size_of::<T>() { Err(bytes) }
    else {
        let (split1, split2) = bytes.split_at_mut(mem::size_of::<T>());
        let result: &mut T = unsafe { mem::transmute(split1.get_unchecked_mut(0)) };
        unsafe { try!(result.exhume(split2)); }
        Ok(result)
    }
}

/// Decodes a binary buffer into a reference to a typed slice.
///
/// `decode_slice` first reads a `&[T]` amount of data from the head of `bytes`, using the length
/// there to read enough additional data from `bytes` to back its memory. It will then `exhume`
/// each element, offering them the ability to consume prefixes of `bytes` to back any owned data.
///
/// #Examples
/// ```
/// use abomonation::{encode_slice, decode_slice};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// encode_slice(&vector, &mut bytes);
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Ok(result) = decode_slice::<(u64, String)>(&mut bytes) {
///     assert!(result == &vector[..]);
/// }
/// ```
pub fn decode_slice<T: Abomonation>(bytes: &mut [u8]) -> Result<&[T], &mut [u8]> {
    if bytes.len() < mem::size_of::<&[T]>() { Err(bytes) }
    else {
        let (split1, split2) = bytes.split_at_mut(mem::size_of::<&[T]>());
        let result: &mut &[T] = unsafe { mem::transmute(split1.get_unchecked_mut(0)) };
        unsafe { try!(result.exhume(split2)); }
        Ok(result)
    }
}


/// Abomonation provides methods to serialize any heap data the implementor owns.
///
/// The default implementations for Abomonation's methods are all empty. Many types have no owned
/// data to transcribe. Some do, however, and need to carefully implement these unsafe methods.
///
/// #Safety
///
/// Abomonation has no safe methods. Please do not call them. They should be called only by
/// `encode` and `decode`, each of which impose restrictions on ownership and lifetime of the data
/// they take as input and return as output.
///
/// If you are concerned about safety, it may be best to avoid Abomonation all together. It does
/// several things that may be undefined behavior, depending on how undefined behavior is defined.
pub trait Abomonation {

    /// Write any additional information about `&self` beyond its binary representation.
    ///
    /// Most commonly this is owned data on the other end of pointers in `&self`.
    unsafe fn entomb(&self, _writer: &mut Vec<u8>) { }

    /// Perform any final edits before committing `&mut self`. Importantly, this method should only
    /// manipulate the fields of `self`; any owned memory may not be valid.
    ///
    /// Most commonly this overwrites pointers whose values should not be serialized.
    unsafe fn embalm(&mut self) { }

    /// Recover any information for `&mut self` not evident from its binary representation.
    ///
    /// Most commonly this populates pointers with valid references into `bytes`.
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> { Ok(bytes) }
}

impl Abomonation for u8 { }
impl Abomonation for u16 { }
impl Abomonation for u32 { }
impl Abomonation for u64 { }

impl Abomonation for i8 { }
impl Abomonation for i16 { }
impl Abomonation for i32 { }
impl Abomonation for i64 { }

impl Abomonation for f32 { }
impl Abomonation for f64 { }

impl Abomonation for bool { }
impl Abomonation for () {}

impl<T: Abomonation> Abomonation for Option<T> { }

impl<T1: Abomonation, T2: Abomonation> Abomonation for (T1, T2) {
    unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); }
    unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {
        let tmp = bytes; bytes = try!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try!(self.1.exhume(tmp));
        Ok(bytes)
    }
}

impl<T1: Abomonation, T2: Abomonation, T3: Abomonation> Abomonation for (T1, T2, T3) {
    unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); self.2.embalm(); }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); self.2.entomb(bytes); }
    unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {
        let tmp = bytes; bytes = try!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try!(self.1.exhume(tmp));
        let tmp = bytes; bytes = try!(self.2.exhume(tmp));
        Ok(bytes)
    }
}

impl<T1: Abomonation, T2: Abomonation, T3: Abomonation, T4: Abomonation> Abomonation for (T1, T2, T3, T4) {
    unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); self.2.embalm(); self.3.embalm(); }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); self.2.entomb(bytes); self.3.entomb(bytes); }
    unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {
        let tmp = bytes; bytes = try!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try!(self.1.exhume(tmp));
        let tmp = bytes; bytes = try!(self.2.exhume(tmp));
        let tmp = bytes; bytes = try!(self.3.exhume(tmp));
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
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {
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
        for element in bytes_to_typed::<T>(&mut bytes[position..], self.len()) { element.embalm(); }
        for element in self.iter() { element.entomb(bytes); }
    }
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {

        // extract memory from bytes to back our vector
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { Err(bytes) }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            std::ptr::write(self, Vec::from_raw_parts(slice.as_mut_ptr(), self.len(), self.len()));
            for element in self.iter_mut() {
                let temp = rest;             // temp variable explains lifetimes (mysterious!)
                rest = try!(element.exhume(temp));
            }
            Ok(rest)
        }
    }
}

impl<'c, T: Abomonation> Abomonation for &'c [T] {
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, std::slice::from_raw_parts(0 as *mut T, self.len()));
    }
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        let position = bytes.len();
        bytes.write_all(typed_to_bytes(self)).unwrap();
        for element in bytes_to_typed::<T>(&mut bytes[position..], self.len()) { element.embalm(); }
        for element in self.iter() { element.entomb(bytes); }
    }
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Result<&'b mut [u8], &'b mut [u8]> {

        // extract memory from bytes to back our slice
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { Err(bytes) }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            for element in slice.iter_mut() {
                let temp = rest;
                rest = try!(element.exhume(temp));
            }
            *self = slice;
            Ok(rest)
        }
    }
}

// currently enables UB, by exposing padding bytes
unsafe fn typed_to_bytes<T>(slice: &[T]) -> &[u8] {
    std::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * mem::size_of::<T>())
}

// takes a len to make working with zero-size types easier
unsafe fn bytes_to_typed<T>(slice: &mut [u8], len: usize) -> &mut [T] {
    std::slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut T, len)
}
