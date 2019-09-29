//! Abomonation (spelling intentional) is a fast serialization / deserialization crate.
//!
//! Abomonation takes typed elements and simply writes their contents as binary.
//! It then gives the element the opportunity to serialize more data, which is
//! useful for types with owned memory such as `String` and `Vec`.
//! The result is effectively a copy of reachable memory.
//! Deserialization results in a shared reference to the type, pointing at the binary data itself.
//!
//! Abomonation does several unsafe things, and should ideally be used only through the methods
//! `encode` and `decode` on types implementing the `Abomonation` trait. Implementing the
//! `Abomonation` trait is highly discouraged; instead, you can use the [`abomonation_derive` crate](https://crates.io/crates/abomonation_derive).
//!
//! **Very important**: Abomonation reproduces the memory as laid out by the serializer, which will
//! reveal architectural variations. Data encoded on a 32bit big-endian machine will not decode
//! properly on a 64bit little-endian machine. Moreover, it could result in undefined behavior if
//! the deserialization results in invalid typed data. Please do not do this.
//!
//!
//! # Examples
//! ```
//! use abomonation::{encode, decode};
//!
//! // create some test data out of abomonation-approved types
//! let vector = (0..256u64).map(|i| (i, format!("{}", i)))
//!                         .collect::<Vec<_>>();
//!
//! // encode a Vec<(u64, String)> into a Vec<u8>
//! let mut bytes = Vec::new();
//! unsafe { encode(&vector, &mut bytes); }
//!
//! // decode a &Vec<(u64, String)> from &mut [u8] binary data
//! if let Some((result, remaining)) = unsafe { decode::<Vec<(u64, String)>>(&mut bytes) } {
//!     assert!(result == &vector);
//!     assert!(remaining.len() == 0);
//! }
//! ```

use std::mem;       // yup, used pretty much everywhere.
use std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.
use std::io::Result as IOResult;
use std::marker::PhantomData;
use std::num::*;
use std::ptr::NonNull;

pub mod abomonated;

/// Encodes a typed reference into a binary buffer.
///
/// # Safety
///
/// This method is unsafe because it is unsafe to transmute typed allocations to binary.
/// Furthermore, Rust currently indicates that it is undefined behavior to observe padding
/// bytes, which will happen when we `memmcpy` structs which contain padding bytes.
///
/// # Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// unsafe { encode(&vector, &mut bytes); }
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Some((result, remaining)) = unsafe { decode::<Vec<(u64, String)>>(&mut bytes) } {
///     assert!(result == &vector);
///     assert!(remaining.len() == 0);
/// }
/// ```
///
#[inline(always)]
pub unsafe fn encode<T: Entomb, W: Write>(typed: &T, mut write: W) -> IOResult<()> {
    let slice = std::slice::from_raw_parts(mem::transmute(typed), mem::size_of::<T>());
    write.write_all(slice)?;
    T::entomb(typed, &mut write)
}

/// Decodes a mutable binary slice into an immutable typed reference.
///
/// `decode` treats the first `mem::size_of::<T>()` bytes as a `T`, and will then `exhume` the
/// element, offering it the ability to consume prefixes of `bytes` to back any owned data.
/// The return value is either a pair of the typed reference `&T` and the remaining `&mut [u8]`
/// binary data, or `None` if decoding failed due to lack of data.
///
/// # Safety
///
/// The `decode` method is unsafe due to a number of unchecked invariants.
///
/// Decoding arbitrary `&[u8]` data can
/// result in invalid utf8 strings, enums with invalid discriminants, etc. `decode` *does*
/// perform bounds checks, as part of determining if enough data are present to completely decode,
/// and while it should only write within the bounds of its `&mut [u8]` argument, the use of invalid
/// utf8 and enums are undefined behavior.
///
/// Please do not decode data that was not encoded by the corresponding implementation.
///
/// In addition, `decode` does not ensure that the bytes representing types will be correctly aligned.
/// On several platforms unaligned reads are undefined behavior, but on several other platforms they
/// are only a performance penalty.
///
/// # Examples
/// ```
/// use abomonation::{encode, decode};
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// unsafe { encode(&vector, &mut bytes); }
///
/// // decode a &Vec<(u64, String)> from &mut [u8] binary data
/// if let Some((result, remaining)) = unsafe { decode::<Vec<(u64, String)>>(&mut bytes) } {
///     assert!(result == &vector);
///     assert!(remaining.len() == 0);
/// }
/// ```
pub unsafe fn decode<'bytes, T>(bytes: &'bytes mut [u8]) -> Option<(&'bytes T, &'bytes mut [u8])>
    where T: Exhume<'bytes>
{
    if bytes.len() < mem::size_of::<T>() { None }
    else {
        let (split1, split2) = bytes.split_at_mut(mem::size_of::<T>());
        let result: NonNull<T> = mem::transmute(split1.get_unchecked_mut(0));
        if let Some(remaining) = T::exhume(result, split2) {
            Some((&*result.as_ptr(), remaining))
        }
        else {
            None
        }
    }
}

/// Reports the number of bytes required to encode `self`.
///
/// # Safety
///
/// The `measure` method is safe. It neither produces nor consults serialized representations.
pub fn measure<T: Entomb>(typed: &T) -> usize {
    mem::size_of::<T>() + T::extent(&typed)
}

/// Abomonation provides methods to serialize any heap data the implementor owns.
///
/// The trait's lifetime parameter `'de` represents the set of slices of bytes `&'de mut [u8]`
/// from which it is valid to deserialize an `&'de impl Abomonation<'de>`. Types which own all of
/// their data may be deserialized freely, and implement this trait for all `'de`. However, we
/// need to enforce some deserialization restrictions on types which contain references.
///
/// The reason is that abomonation performes in-place deserialization. To do that, it has to
/// patch a type's reference to point to other serialized data. Where a type _should_ contain an
/// `&'a T`, abomonation patches that into an `&'de T`. For this substitution to be valid, we
/// need `'de` to outlive `'a`. Otherwise, a careless user could ask abomonation to deserialize a
/// `&'static T` and get a `&'de T` which masquerades as an `&'static T` instead. The user could
/// then copy this reference, drop the bytes, and get use-after-free undefined behavior.
///
/// The default implementations for Abomonation's methods are all empty. Many types have no owned
/// data to transcribe. Some do, however, and need to carefully implement these unsafe methods.
///
/// # Safety
///
/// `entomb` and `exhume` are not meant to be called directly. They should be called only by
/// `encode` and `decode`, each of which impose restrictions on ownership and lifetime of the data
/// they take as input and return as output, thus improving safety.
///
/// Not all Rust types are abomonable, and one should think carefully about the implications of
/// implementing `Abomonation` for a type. To lend itself to this exercise, a type must...
///
/// - Provide exhaustive access to its internal representation
/// - Allow reconstruction from said representation
/// - Survive having its heap allocations being silently replaced by inline pointers to
///   the same storage block, as long as only a shared reference is observed.
///
/// The last point is the reason why `Abomonation` only provides a shared reference to the
/// reconstructed object. Without this, it would be trivial to trigger, say, a `Box` destructor
/// that tries to call `free()` on the inner pointer. But the use of a shared reference only
/// provides minimal sanity, and for types with internal mutability (those with an `UnsafeCell`
/// inside), this precaution is insufficient. `Abomonation` is generally not safely implementable
/// for such types, but may work in particular cases like atomics.
///
/// If you are concerned about safety, it may be best to avoid Abomonation all together. It does
/// several things that may be undefined behavior, depending on how undefined behavior is defined.
pub unsafe trait Abomonation<'de> : Entomb + Exhume<'de> {}
unsafe impl<'de, T: Entomb + Exhume<'de>> Abomonation<'de> for T {}

/// Types which can be serialized into bytes by abomonation
///
/// Please consult the Abomonation trait's documentation for more details. Most
/// types which are serializable by abomonation are also deserializable by
/// abomonation, but we need to have a separate serialization and
/// deserialization trait for obscure lifetime-related reasons.
///
pub unsafe trait Entomb {
    /// Write any additional information about `&self` beyond its binary representation.
    ///
    /// Most commonly this is owned data on the other end of pointers in `&self`. The return value
    /// reports any failures in writing to `write`.
    unsafe fn entomb<W: Write>(&self, _write: &mut W) -> IOResult<()> { Ok(()) }

    /// Reports the number of further bytes required to entomb `self`.
    fn extent(&self) -> usize { 0 }
}

/// Types which can be deserialized from `&'de mut [u8]` to `&'de T` by abomonation
///
/// Please consult the Abomonation trait's documentation for more details. Most
/// types which are serializable by abomonation are also deserializable by
/// abomonation, but we need to have a separate serialization and
/// deserialization trait for obscure lifetime-related reasons.
///
pub unsafe trait Exhume<'de> : Entomb + 'de {
    /// Recover any information for `self_` not evident from its binary representation.
    ///
    /// Most commonly this populates pointers with valid references into `bytes`.
    ///
    /// Implementors should take note that `self_` is initially in an invalid state, as its inner
    /// pointers may be dangling. As Rust references come with a data validity invariant, building
    /// references to invalid state is undefined behavior, so one should strive to implement
    /// `exhume` using raw pointer operations as much as feasible.
    //
    // FIXME: Replace self_ with self once Rust has arbitrary self types
    unsafe fn exhume(_self_: NonNull<Self>, bytes: &'de mut [u8]) -> Option<&'de mut [u8]> { Some(bytes) }
}

/// The `unsafe_abomonate!` macro takes a type name with an optional list of fields, and implements
/// `Abomonation` for the type, following the pattern of the tuple implementations: each method
/// calls the equivalent method on each of its fields.
///
/// It is strongly recommended that you use the `abomonation_derive` crate instead of this macro.
///
/// # Safety
/// `unsafe_abomonate` is unsafe because if you fail to specify a field it will not be properly
/// re-initialized from binary data. This can leave you with a dangling pointer, or worse.
///
/// # Examples
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
///     unsafe { encode(&my_struct, &mut bytes); }
///
///     // decode a &MyStruct from &mut [u8] binary data
///     if let Some((result, remaining)) = unsafe { decode::<MyStruct>(&mut bytes) } {
///         assert!(result == &my_struct);
///         assert!(remaining.len() == 0);
///     }
/// }
/// ```
#[macro_export]
#[deprecated(since="0.5", note="please use the abomonation_derive crate")]
macro_rules! unsafe_abomonate {
    ($t:ty) => {
        unsafe impl $crate::Entomb for $t { }
        unsafe impl $crate::Exhume<'_> for $t { }
    };
    ($t:ty : $($field:ident),*) => {
        unsafe impl $crate::Entomb for $t {
            unsafe fn entomb<W: ::std::io::Write>(&self, write: &mut W) -> ::std::io::Result<()> {
                $( $crate::Entomb::entomb(&self.$field, write)?; )*
                Ok(())
            }

            fn extent(&self) -> usize {
                let mut size = 0;
                $( size += $crate::Entomb::extent(&self.$field); )*
                size
            }
        }

        unsafe impl<'de> $crate::Exhume<'de> for $t {
            unsafe fn exhume(self_: ::std::ptr::NonNull<Self>, mut bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
                $(
                    // FIXME: This (briefly) constructs an &mut _ to invalid data, which is UB.
                    //        The proposed &raw mut operator would allow avoiding this.
                    let field_ptr: ::std::ptr::NonNull<_> = From::from(&mut (*self_.as_ptr()).$field);
                    bytes = $crate::Exhume::exhume(field_ptr, bytes)?;
                )*
                Some(bytes)
            }
        }
    };
}

// general code for tuples (can't use '0', '1', ... as field identifiers)
macro_rules! tuple_abomonate {
    ( $($ty:ident)+) => (
        unsafe impl<$($ty: Entomb),*> Entomb for ($($ty,)*) {
            #[allow(non_snake_case)]
            unsafe fn entomb<WRITE: Write>(&self, write: &mut WRITE) -> IOResult<()> {
                let ($(ref $ty,)*) = *self;
                $( $ty::entomb($ty, write)?; )*
                Ok(())
            }

            #[allow(non_snake_case)]
            fn extent(&self) -> usize {
                let mut size = 0;
                let ($(ref $ty,)*) = *self;
                $( size += $ty::extent($ty); )*
                size
            }
        }

        unsafe impl<'de, $($ty: Exhume<'de>),*> Exhume<'de> for ($($ty,)*) {
            #[allow(non_snake_case)]
            unsafe fn exhume(self_: NonNull<Self>, mut bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
                // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
                //        I think avoiding this would require a cleaner way to iterate over tuple fields.
                //        One possibility would be a C++11-style combination of variadic generics and recursion.
                let ($(ref mut $ty,)*) = *self_.as_ptr();
                $(
                    let field_ptr : NonNull<$ty> = From::from($ty);
                    bytes = $ty::exhume(field_ptr, bytes)?;
                )*
                Some(bytes)
            }
        }
    );
}

unsafe impl Entomb for u8 {}
unsafe impl Exhume<'_> for u8 {}
unsafe impl Entomb for u16 {}
unsafe impl Exhume<'_> for u16 {}
unsafe impl Entomb for u32 {}
unsafe impl Exhume<'_> for u32 {}
unsafe impl Entomb for u64 {}
unsafe impl Exhume<'_> for u64 {}
unsafe impl Entomb for u128 {}
unsafe impl Exhume<'_> for u128 {}
unsafe impl Entomb for usize {}
unsafe impl Exhume<'_> for usize {}

unsafe impl Entomb for i8 {}
unsafe impl Exhume<'_> for i8 {}
unsafe impl Entomb for i16 {}
unsafe impl Exhume<'_> for i16 {}
unsafe impl Entomb for i32 {}
unsafe impl Exhume<'_> for i32 {}
unsafe impl Entomb for i64 {}
unsafe impl Exhume<'_> for i64 {}
unsafe impl Entomb for i128 {}
unsafe impl Exhume<'_> for i128 {}
unsafe impl Entomb for isize {}
unsafe impl Exhume<'_> for isize {}

unsafe impl Entomb for NonZeroU8 {}
unsafe impl Exhume<'_> for NonZeroU8 {}
unsafe impl Entomb for NonZeroU16 {}
unsafe impl Exhume<'_> for NonZeroU16 {}
unsafe impl Entomb for NonZeroU32 {}
unsafe impl Exhume<'_> for NonZeroU32 {}
unsafe impl Entomb for NonZeroU64 {}
unsafe impl Exhume<'_> for NonZeroU64 {}
unsafe impl Entomb for NonZeroU128 {}
unsafe impl Exhume<'_> for NonZeroU128 {}
unsafe impl Entomb for NonZeroUsize {}
unsafe impl Exhume<'_> for NonZeroUsize {}

unsafe impl Entomb for NonZeroI8 {}
unsafe impl Exhume<'_> for NonZeroI8 {}
unsafe impl Entomb for NonZeroI16 {}
unsafe impl Exhume<'_> for NonZeroI16 {}
unsafe impl Entomb for NonZeroI32 {}
unsafe impl Exhume<'_> for NonZeroI32 {}
unsafe impl Entomb for NonZeroI64 {}
unsafe impl Exhume<'_> for NonZeroI64 {}
unsafe impl Entomb for NonZeroI128 {}
unsafe impl Exhume<'_> for NonZeroI128 {}
unsafe impl Entomb for NonZeroIsize {}
unsafe impl Exhume<'_> for NonZeroIsize {}

unsafe impl Entomb for f32 {}
unsafe impl Exhume<'_> for f32 {}
unsafe impl Entomb for f64 {}
unsafe impl Exhume<'_> for f64 {}

unsafe impl Entomb for bool {}
unsafe impl Exhume<'_> for bool {}
unsafe impl Entomb for () {}
unsafe impl Exhume<'_> for () {}

unsafe impl Entomb for char {}
unsafe impl Exhume<'_> for char {}

unsafe impl Entomb for ::std::time::Duration {}
unsafe impl Exhume<'_> for ::std::time::Duration {}

unsafe impl<T> Entomb for PhantomData<T> {}
unsafe impl<'de, T: 'de> Exhume<'de> for PhantomData<T> {}

unsafe impl<T: Entomb> Entomb for Option<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        if let &Some(ref inner) = self {
            T::entomb(inner, write)?;
        }
        Ok(())
    }

    fn extent(&self) -> usize {
        self.as_ref().map(T::extent).unwrap_or(0)
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Option<T> {
    unsafe fn exhume(self_: NonNull<Self>, mut bytes: &'de mut[u8]) -> Option<&'de mut [u8]> {
        // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on enum implementation details.
        if let Some(ref mut inner) = *self_.as_ptr() {
            let inner_ptr : NonNull<T> = From::from(inner);
            bytes = T::exhume(inner_ptr, bytes)?;
        }
        Some(bytes)
    }
}

unsafe impl<T: Entomb, E: Entomb> Entomb for Result<T, E> {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        match self {
            &Ok(ref inner) => T::entomb(inner, write),
            &Err(ref inner) => E::entomb(inner, write),
        }
    }

    fn extent(&self) -> usize {
        match self {
            &Ok(ref inner) => T::extent(inner),
            &Err(ref inner) => E::extent(inner),
        }
    }
}
unsafe impl<'de, T: Exhume<'de>, E: Exhume<'de>> Exhume<'de> for Result<T, E> {
    unsafe fn exhume(self_: NonNull<Self>, bytes: &'de mut[u8]) -> Option<&'de mut [u8]> {
        // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on enum implementation details.
        match *self_.as_ptr() {
            Ok(ref mut inner) => {
                let inner_ptr : NonNull<T> = From::from(inner);
                T::exhume(inner_ptr, bytes)
            }
            Err(ref mut inner) => {
                let inner_ptr : NonNull<E> = From::from(inner);
                E::exhume(inner_ptr, bytes)
            }
        }
    }
}

tuple_abomonate!(A);
tuple_abomonate!(A B);
tuple_abomonate!(A B C);
tuple_abomonate!(A B C D);
tuple_abomonate!(A B C D E);
tuple_abomonate!(A B C D E F);
tuple_abomonate!(A B C D E F G);
tuple_abomonate!(A B C D E F G H);
tuple_abomonate!(A B C D E F G H I);
tuple_abomonate!(A B C D E F G H I J);
tuple_abomonate!(A B C D E F G H I J K);
tuple_abomonate!(A B C D E F G H I J K L);
tuple_abomonate!(A B C D E F G H I J K L M);
tuple_abomonate!(A B C D E F G H I J K L M N);
tuple_abomonate!(A B C D E F G H I J K L M N O);
tuple_abomonate!(A B C D E F G H I J K L M N O P);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD AE);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD AE AF);

macro_rules! array_abomonate {
    ($size:expr) => (
        unsafe impl<T: Entomb> Entomb for [T; $size] {
            unsafe fn entomb<W: Write>(&self, write: &mut W) ->  IOResult<()> {
                entomb_slice(&self[..], write)
            }

            fn extent(&self) -> usize {
                slice_extent(&self[..])
            }
        }

        unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for [T; $size] {
            unsafe fn exhume(self_: NonNull<Self>, bytes: &'de mut[u8]) -> Option<&'de mut [u8]> {
                exhume_slice(self_.as_ptr() as *mut T, $size, bytes)
            }
        }
    )
}

array_abomonate!(0);
array_abomonate!(1);
array_abomonate!(2);
array_abomonate!(3);
array_abomonate!(4);
array_abomonate!(5);
array_abomonate!(6);
array_abomonate!(7);
array_abomonate!(8);
array_abomonate!(9);
array_abomonate!(10);
array_abomonate!(11);
array_abomonate!(12);
array_abomonate!(13);
array_abomonate!(14);
array_abomonate!(15);
array_abomonate!(16);
array_abomonate!(17);
array_abomonate!(18);
array_abomonate!(19);
array_abomonate!(20);
array_abomonate!(21);
array_abomonate!(22);
array_abomonate!(23);
array_abomonate!(24);
array_abomonate!(25);
array_abomonate!(26);
array_abomonate!(27);
array_abomonate!(28);
array_abomonate!(29);
array_abomonate!(30);
array_abomonate!(31);
array_abomonate!(32);

unsafe impl Entomb for String {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(self.as_bytes())
    }

    fn extent(&self) -> usize {
        self.len()
    }
}
unsafe impl<'de> Exhume<'de> for String {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
        // FIXME: This (briefly) constructs an &String to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on String implementation details.
        let self_len = self_.as_ref().len();
        if self_len > bytes.len() { None }
        else {
            let (mine, rest) = bytes.split_at_mut(self_len);
            self_.as_ptr().write(String::from_raw_parts(mine.as_mut_ptr(), self_len, self_len));
            Some(rest)
        }
    }
}

unsafe impl<T: Entomb> Entomb for Vec<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(typed_to_bytes(&self[..]))?;
        entomb_slice(&self[..], write)
    }

    fn extent(&self) -> usize {
        mem::size_of::<T>() * self.len() + slice_extent(&self[..])
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Vec<T> {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
        // FIXME: This (briefly) constructs an &Vec<T> to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on Vec implementation details.
        let self_len = self_.as_ref().len();
        let binary_len = self_len * mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let first_ptr = mine.as_mut_ptr() as *mut T;
            rest = exhume_slice(first_ptr, self_len, rest)?;
            self_.as_ptr().write(Vec::from_raw_parts(first_ptr, self_len, self_len));
            Some(rest)
        }
    }
}

unsafe impl<T: Entomb> Entomb for Box<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(typed_to_bytes(std::slice::from_ref(&**self)))?;
        T::entomb(&**self, write)
    }

    fn extent(&self) -> usize {
        mem::size_of::<T>() + T::extent(&**self)
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Box<T> {
    unsafe fn exhume(self_: NonNull<Self>, bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
        let binary_len = mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let box_target : NonNull<T> = NonNull::new_unchecked(mine.as_mut_ptr() as *mut T);
            rest = T::exhume(box_target, rest)?;
            self_.as_ptr().write(Box::from_raw(box_target.as_ptr()));
            Some(rest)
        }
    }
}

// This method currently enables undefined behavior, by exposing padding bytes.
unsafe fn typed_to_bytes<T>(slice: &[T]) -> &[u8] {
    std::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * mem::size_of::<T>())
}

// Common subset of "entomb" for all [T]-like types
unsafe fn entomb_slice<T: Entomb, W: Write>(slice: &[T], write: &mut W) -> IOResult<()> {
    for element in slice { T::entomb(element, write)?; }
    Ok(())
}

// Common subset of "extent" for all [T]-like types
fn slice_extent<T: Entomb>(slice: &[T]) -> usize {
    slice.iter().map(T::extent).sum()
}

// Common subset of "exhume" for all [T]-like types
// (I'd gladly take a NonNull<[T]>, but it is too difficult to build raw pointers to slices)
#[inline]
unsafe fn exhume_slice<'de, T: Exhume<'de>>(
    first_ptr: *mut T,
    length: usize,
    mut bytes: &'de mut [u8]
) -> Option<&'de mut [u8]> {
    for i in 0..length {
        let element_ptr: NonNull<T> = NonNull::new_unchecked(first_ptr.add(i));
        bytes = T::exhume(element_ptr, bytes)?;
    }
    Some(bytes)
}

mod network {
    use super::{Entomb, Exhume};
    use std::net::{SocketAddr, SocketAddrV4, SocketAddrV6, IpAddr, Ipv4Addr, Ipv6Addr};

    unsafe impl Entomb for IpAddr {}
    unsafe impl Exhume<'_> for IpAddr {}
    unsafe impl Entomb for Ipv4Addr {}
    unsafe impl Exhume<'_> for Ipv4Addr {}
    unsafe impl Entomb for Ipv6Addr {}
    unsafe impl Exhume<'_> for Ipv6Addr {}

    unsafe impl Entomb for SocketAddr {}
    unsafe impl Exhume<'_> for SocketAddr {}
    unsafe impl Entomb for SocketAddrV4 {}
    unsafe impl Exhume<'_> for SocketAddrV4 {}
    unsafe impl Entomb for SocketAddrV6 {}
    unsafe impl Exhume<'_> for SocketAddrV6 {}
}
