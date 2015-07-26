//! Abomonation (spelling intentional) is a fast serialization / deserialization crate.
//!
//! Abomonation takes typed elements and simply writes their contents as binary.
//! It then gives the element the opportunity to serialize more data, which is
//! useful for types with owned memory such as `String` and `Vec`.
//! The result is effectively a copy of reachable memory, where pointers are zero-ed out and vector
//! capacities are set to the vector length.
//! Deserialization results in a shared reference to the type, pointing at the binary data itself.
//!
//! Abomonation does several unsafe things, and should ideally be used only through the methods
//! `encode` and `decode` on types implementing the `Abomonation` trait. Implementing the
//! `Abomonation` trait is highly discouraged, unless you use the `abomonate!` macro
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
//! // decode a &Vec<(u64, String)> from &mut [u8] binary data
//! if let Some((result, remaining)) = decode::<Vec<(u64, String)>>(&mut bytes) {
//!     assert!(result == &vector);
//!     assert!(remaining.len() == 0);
//! }
//! ```

use std::mem;       // yup, used pretty much everywhere.
use std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.

const EMPTY: *mut () = 0x1 as *mut ();

macro_rules! try_option {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => { return None }
    })
}

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
/// if let Some((result, remaining)) = decode::<Vec<(u64, String)>>(&mut bytes) {
///     assert!(result == &vector);
///     assert!(remaining.len() == 0);
/// }
/// ```
///
#[inline]
pub fn encode<T: Abomonation>(typed: &T, bytes: &mut Vec<u8>) {
    unsafe {
        let start = bytes.len();            // may not be empty!
        let slice = std::slice::from_raw_parts(mem::transmute(typed), mem::size_of::<T>());
        bytes.write_all(slice).unwrap();    // Rust claims a write to a Vec<u8> will never fail.
        let result: &mut T = mem::transmute(bytes.as_mut_ptr().offset(start as isize));
        result.embalm();
        typed.entomb(bytes);
    }
}

/// Decodes a binary buffer into a reference to a typed element.
///
/// `decode` treats the first `mem::size_of::<T>()` bytes as a `T`, and will then `exhume` the
/// element, offering it the ability to consume prefixes of `bytes` to back any owned data.
/// The return value is either a pair of the typed reference `&T` and the remaining `&mut [u8]`
/// binary data if the deserialization found enough data, or the remaining `&mut [u8]` at the
/// point where it ran out of data.
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
/// if let Some((result, remaining)) = decode::<Vec<(u64, String)>>(&mut bytes) {
///     assert!(result == &vector);
///     assert!(remaining.len() == 0);
/// }
/// ```
#[inline]
pub fn decode<T: Abomonation>(bytes: &mut [u8]) -> Option<(&T, &mut [u8])> {
    if bytes.len() < mem::size_of::<T>() { None }
    else {
        let (split1, split2) = bytes.split_at_mut(mem::size_of::<T>());
        let result: &mut T = unsafe { mem::transmute(split1.get_unchecked_mut(0)) };
        if let Some(remaining) = unsafe { result.exhume(split2) } {
            Some((result, remaining))
        }
        else {
            None
        }
    }
}

/// Decodes a binary buffer into a reference to a typed element *without* validating the data .
///
/// `decode_unchecked` is meant to be used on buffers that have had `decode` called on them.
/// Performance is not the main reason (`decode`) is generally very fast, but rather that
/// the method can take a shared reference, without needing to mutate the underlying buffer.
///
/// #Examples
/// ```
/// use abomonation::{encode, decode, decode_unchecked};
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
/// assert!(decode::<Vec<(u64, String)>>(&mut bytes).is_some());
///
/// // remove mutability
/// let bytes = bytes;
/// unsafe {
///     assert!(decode_unchecked::<Vec<(u64, String)>>(&bytes) == &vector);
/// }
/// ```
#[inline]
pub unsafe fn decode_unchecked<T: Abomonation>(bytes: &[u8]) -> &T {
    // TODO : we could validate bytes, with additions to Abomonation
    mem::transmute(bytes.get_unchecked(0))
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
    #[inline] unsafe fn entomb(&self, _writer: &mut Vec<u8>) { }

    /// Perform any final edits before committing `&mut self`. Importantly, this method should only
    /// manipulate the fields of `self`; any owned memory may not be valid.
    ///
    /// Most commonly this overwrites pointers whose values should not be serialized.
    #[inline] unsafe fn embalm(&mut self) { }

    /// Recover any information for `&mut self` not evident from its binary representation.
    ///
    /// Most commonly this populates pointers with valid references into `bytes`.
    #[inline] unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> { Some(bytes) }
}

/// The `unsafe_abomonate!` macro takes a type name with an optional list of fields, and implements
/// 'Abomonation' for the type, following the pattern of the tuple implementations: each method
/// calls the equivalent method on each of its fields.
///
/// #Safety
/// `unsafe_abomonate` is unsafe because if you fail to specify a field it will not be properly
/// re-initialized from binary data. This can leave you with a dangling pointer, or worse.
///
/// #Examples
/// ```
/// #[macro_use]
/// extern crate abomonation;
/// use abomonation::{encode, decode, Abomonation};
///
/// #[derive(Eq, PartialEq)]
/// struct MyStruct {
///     a: String,
///     b: u64,
///     c: Vec<u8>,
/// }
///
/// unsafe_abomonate!(MyStruct : a, b, c);
///
/// fn main() {
///
///     // create some test data out of recently-abomonable types
///     let my_struct = MyStruct { a: "grawwwwrr".to_owned(), b: 0, c: vec![1,2,3] };
///
///     // encode a &MyStruct into a Vec<u8>
///     let mut bytes = Vec::new();
///     encode(&my_struct, &mut bytes);
///
///     // decode a &MyStruct from &mut [u8] binary data
///     if let Some((result, remaining)) = decode::<MyStruct>(&mut bytes) {
///         assert!(result == &my_struct);
///         assert!(remaining.len() == 0);
///     }
/// }
/// ```
#[macro_export]
macro_rules! unsafe_abomonate {
    ($t:ty) => { impl Abomonation for $t { } };
    ($t:ty : $($field:ident),*) => {
        impl Abomonation for $t {
            #[inline] unsafe fn entomb(&self, _writer: &mut Vec<u8>) {
                $( self.$field.entomb(_writer); )*
            }
            #[inline] unsafe fn embalm(&mut self) {
                $( self.$field.embalm(); )*
            }
            #[inline] unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
                $( let temp = bytes; bytes = if let Some(bytes) = self.$field.exhume(temp) { bytes} else { return None }; )*
                Some(bytes)
            }
        }
    }
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

impl<T: Abomonation> Abomonation for Option<T> {
    #[inline] unsafe fn embalm(&mut self) {
        if let &mut Some(ref mut inner) = self {
            inner.embalm();
        }
    }
    #[inline] unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        if let &Some(ref inner) = self {
            inner.entomb(bytes);
        }
    }
    #[inline] unsafe fn exhume<'a, 'b>(&'a mut self, mut bytes: &'b mut[u8]) -> Option<&'b mut [u8]> {
        if let &mut Some(ref mut inner) = self {
            let tmp = bytes; bytes = try_option!(inner.exhume(tmp));
        }
        Some(bytes)
    }
}

impl<T1: Abomonation, T2: Abomonation> Abomonation for (T1, T2) {
    #[inline] unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); }
    #[inline] unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); }
    #[inline] unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        let tmp = bytes; bytes = try_option!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.1.exhume(tmp));
        Some(bytes)
    }
}

impl<T1: Abomonation, T2: Abomonation, T3: Abomonation> Abomonation for (T1, T2, T3) {
    #[inline] unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); self.2.embalm(); }
    #[inline] unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); self.2.entomb(bytes); }
    #[inline] unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        let tmp = bytes; bytes = try_option!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.1.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.2.exhume(tmp));
        Some(bytes)
    }
}

impl<T1: Abomonation, T2: Abomonation, T3: Abomonation, T4: Abomonation> Abomonation for (T1, T2, T3, T4) {
    #[inline] unsafe fn embalm(&mut self) { self.0.embalm(); self.1.embalm(); self.2.embalm(); self.3.embalm(); }
    #[inline] unsafe fn entomb(&self, bytes: &mut Vec<u8>) { self.0.entomb(bytes); self.1.entomb(bytes); self.2.entomb(bytes); self.3.entomb(bytes); }
    #[inline] unsafe fn exhume<'a,'b>(&'a mut self, mut bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        let tmp = bytes; bytes = try_option!(self.0.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.1.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.2.exhume(tmp));
        let tmp = bytes; bytes = try_option!(self.3.exhume(tmp));
        Some(bytes)
    }
}

impl Abomonation for String {
    #[inline]
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, String::from_raw_parts(EMPTY as *mut u8, self.len(), self.len()));
    }
    #[inline]
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        bytes.write_all(self.as_bytes()).unwrap();
    }
    #[inline]
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        if self.len() > bytes.len() { None }
        else {
            let (mine, rest) = bytes.split_at_mut(self.len());
            std::ptr::write(self, String::from_raw_parts(mem::transmute(mine.as_ptr()), self.len(), self.len()));
            Some(rest)
        }
    }
}

impl<T: Abomonation> Abomonation for Vec<T> {
    #[inline]
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, Vec::from_raw_parts(EMPTY as *mut T, self.len(), self.len()));
    }
    #[inline]
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        let position = bytes.len();
        bytes.write_all(typed_to_bytes(&self[..])).unwrap();
        for element in bytes_to_typed::<T>(&mut bytes[position..], self.len()) { element.embalm(); }
        for element in self.iter() { element.entomb(bytes); }
    }
    #[inline]
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {

        // extract memory from bytes to back our vector
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            std::ptr::write(self, Vec::from_raw_parts(slice.as_mut_ptr(), self.len(), self.len()));
            for element in self.iter_mut() {
                let temp = rest;             // temp variable explains lifetimes (mysterious!)
                rest = try_option!(element.exhume(temp));
            }
            Some(rest)
        }
    }
}

impl<'c, T: Abomonation> Abomonation for &'c [T] {
    #[inline]
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, std::slice::from_raw_parts(EMPTY as *mut T, self.len()));
    }
    #[inline]
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        let position = bytes.len();
        bytes.write_all(typed_to_bytes(self)).unwrap();
        for element in bytes_to_typed::<T>(&mut bytes[position..], self.len()) { element.embalm(); }
        for element in self.iter() { element.entomb(bytes); }
    }
    #[inline]
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {

        // extract memory from bytes to back our slice
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            for element in slice.iter_mut() {
                let temp = rest;
                rest = try_option!(element.exhume(temp));
            }
            *self = slice;
            Some(rest)
        }
    }
}

impl<T: Abomonation> Abomonation for Box<T> {
    #[inline]
    unsafe fn embalm(&mut self) {
        std::ptr::write(self, mem::transmute(EMPTY as *mut T));
    }
    #[inline]
    unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        let position = bytes.len();
        bytes.write_all(std::slice::from_raw_parts(mem::transmute(&**self), mem::size_of::<T>())).unwrap();
        bytes_to_typed::<T>(&mut bytes[position..], 1)[0].embalm();
        (**self).entomb(bytes);
    }
    #[inline]
    unsafe fn exhume<'a,'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        let binary_len = mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            std::ptr::write(self, mem::transmute(mine.as_mut_ptr() as *mut T));
            let temp = rest; rest = try_option!((**self).exhume(temp));
            Some(rest)
        }
    }
}

// currently enables UB, by exposing padding bytes
#[inline] unsafe fn typed_to_bytes<T>(slice: &[T]) -> &[u8] {
    std::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * mem::size_of::<T>())
}

// takes a len to make working with zero-size types easier
#[inline] unsafe fn bytes_to_typed<T>(slice: &mut [u8], len: usize) -> &mut [T] {
    std::slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut T, len)
}
