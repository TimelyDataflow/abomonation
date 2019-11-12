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

use std::mem;
use std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.
use std::io::Result as IOResult;
use std::marker::PhantomData;
use std::num::*;
use std::ptr::NonNull;

pub mod abomonated;
pub mod align;

#[deprecated(note = "Made pub for internal unsafe_abomonate use only")]
pub use align::{AlignedReader, AlignedWriter};

/// Encodes a typed reference into a binary buffer.
///
/// # Safety
///
/// This method is unsafe because Rust currently specifies that it is undefined
/// behavior to construct an `&[u8]` to padding bytes, which will happen when we
/// write down binary data of a type T which contains padding bytes as we must
/// pass down an `&[u8]` to the `Write` API.
///
/// Eliminating this UB will require changes to the Rust languages or `std` to
/// add either of 1/a non-UB way to turn padding bytes into `&[u8]` or 2/a way
/// to send an `&[MaybeUninit<u8>]` (which allows padding bytes) to a Write
/// implementation. See the following discussion thread for more info:
/// https://internals.rust-lang.org/t/writing-down-binary-data-with-padding-bytes/11197/
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
pub unsafe fn encode<T: Entomb, W: Write>(typed: &T, write: W) -> IOResult<()> {
    let mut writer = AlignedWriter::new(write, T::alignment());
    writer.write::<T>(typed)?;
    T::entomb(typed, &mut writer)
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
/// ## Data validity
///
/// `decode()` does not check that the input bytes uphold T's validity
/// invariants. Decoding arbitrary `&[u8]` data can result in invalid
/// utf8 strings, enums with invalid discriminants, null references, etc. and
/// some forms of broken invariants are undefined behavior in Rust.
///
/// `decode` *does* perform bounds checks, as part of determining if enough data
/// are present to completely decode, so it should only read and write within
/// the bounds of its `&mut [u8]` argument. But that only prevents UB for
/// truncated data, not arbitrary invalid data.
///
/// Therefore, please do not decode data that was not encoded by the
/// corresponding encode() implementation.
///
/// ## Alignment
///
/// `decode()` assumes that the input bytes follow the alignment requirements of
/// abomonated data of type T, which you can check with `T::alignment()`.
/// Failure to meet this requirement will result in undefined behavior.
///
/// If you are not able to guarantee sufficient alignment from your data source, you may find the
/// `align::AlignedBytes<T>` utility useful. It checks if your data is well-aligned, and moves it
/// into a well-aligned heap allocation otherwise.
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
    let mut reader = AlignedReader::new(bytes, T::alignment());
    let result_ptr = reader.read::<T>()?;
    Some((T::exhume(result_ptr, &mut reader)?, reader.remaining()))
}

/// Reports the number of bytes required to encode `self`.
///
/// # Safety
///
/// The `measure` method is safe. It neither produces nor consults serialized representations.
pub fn measure<T: Entomb>(typed: &T) -> usize {
    let mut aligned_sink = AlignedWriter::new(std::io::sink(), T::alignment());
    unsafe { encode(typed, &mut aligned_sink).expect("Sink should be infaillible"); }
    aligned_sink.written_so_far()
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
    unsafe fn entomb<W: Write>(&self, _write: &mut AlignedWriter<W>) -> IOResult<()> { Ok(()) }

    /// Report the alignment of the complete Abomonation-serialized data
    fn alignment() -> usize
        where Self: Sized
    { mem::align_of::<Self>() }

    /// Version of "alignment" that takes a &self parameter for use in
    /// declarative macros.
    ///
    /// This is _not_ analogous to `mem::align_of_val` and is only intended for
    /// the internal consumption of the deprecated `unsafe_abomonate` macro.
    /// Please do not use this trait method in any other code.
    ///
    #[deprecated(note="For internal use of unsafe_abomonate only")]
    fn alignment_from_self_ref(&self) -> usize
        where Self: Sized
    { Self::alignment() }
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
    unsafe fn exhume(self_: NonNull<Self>, _reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> { Some(&mut *self_.as_ptr()) }
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
            #[allow(deprecated)]
            unsafe fn entomb<W: ::std::io::Write>(&self, write: &mut $crate::AlignedWriter<W>) -> ::std::io::Result<()> {
                $( $crate::Entomb::entomb(&self.$field, write)?; )*
                Ok(())
            }

            #[allow(deprecated)]
            fn alignment() -> usize {
                // This is ugly, but I can't think about a better way to do this
                // in a declarative macro-based code generator...
                let bad_ref: &Self = unsafe { &*::std::ptr::NonNull::dangling().as_ptr() };
                let mut align = ::std::mem::align_of::<Self>();
                $( align = align.max(bad_ref.$field.alignment_from_self_ref()); )*
                align
            }
        }

        unsafe impl<'de> $crate::Exhume<'de> for $t {
            #[allow(deprecated)]
            unsafe fn exhume(self_: ::std::ptr::NonNull<Self>, reader: &mut $crate::AlignedReader<'de>) -> Option<&'de mut Self> {
                $(
                    // FIXME: This (briefly) constructs an &mut _ to invalid data, which is UB.
                    //        The proposed &raw mut operator would allow avoiding this.
                    let field_ptr: ::std::ptr::NonNull<_> = From::from(&mut (*self_.as_ptr()).$field);
                    $crate::Exhume::exhume(field_ptr, reader)?;
                )*
                Some(&mut *self_.as_ptr())
            }
        }
    };
}

// general code for tuples (can't use '0', '1', ... as field identifiers)
macro_rules! tuple_abomonate {
    ( $($ty:ident)+) => (
        unsafe impl<$($ty: Entomb),*> Entomb for ($($ty,)*) {
            #[allow(non_snake_case)]
            unsafe fn entomb<WRITE: Write>(&self, write: &mut AlignedWriter<WRITE>) -> IOResult<()> {
                let ($(ref $ty,)*) = *self;
                $( $ty::entomb($ty, write)?; )*
                Ok(())
            }

            #[allow(non_snake_case)]
            fn alignment() -> usize {
                let mut align = mem::align_of::<Self>();
                $( align = align.max($ty::alignment()); )*
                align
            }
        }

        unsafe impl<'de, $($ty: Exhume<'de>),*> Exhume<'de> for ($($ty,)*) {
            #[allow(non_snake_case)]
            unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
                // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
                //        I think avoiding this would require a cleaner way to iterate over tuple fields.
                //        One possibility would be a C++11-style combination of variadic generics and recursion.
                let ($(ref mut $ty,)*) = *self_.as_ptr();
                $(
                    let field_ptr : NonNull<$ty> = From::from($ty);
                    $ty::exhume(field_ptr, reader)?;
                )*
                Some(&mut *self_.as_ptr())
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
unsafe impl Entomb for str { fn alignment() -> usize { mem::align_of::<[u8; 1]>() } }
unsafe impl Exhume<'_> for str {}

unsafe impl Entomb for ::std::time::Duration {}
unsafe impl Exhume<'_> for ::std::time::Duration {}

unsafe impl<T> Entomb for PhantomData<T> {}
unsafe impl<'de, T: 'de> Exhume<'de> for PhantomData<T> {}

unsafe impl<T: Entomb> Entomb for Option<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        if let &Some(ref inner) = self {
            T::entomb(inner, write)?;
        }
        Ok(())
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(T::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Option<T> {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on enum implementation details.
        if let Some(ref mut inner) = *self_.as_ptr() {
            let inner_ptr : NonNull<T> = From::from(inner);
            T::exhume(inner_ptr, reader)?;
        }
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<T: Entomb, E: Entomb> Entomb for Result<T, E> {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        match self {
            &Ok(ref inner) => T::entomb(inner, write),
            &Err(ref inner) => E::entomb(inner, write),
        }
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(T::alignment()).max(E::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>, E: Exhume<'de>> Exhume<'de> for Result<T, E> {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs a "ref mut" to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on enum implementation details.
        match *self_.as_ptr() {
            Ok(ref mut inner) => {
                let inner_ptr : NonNull<T> = From::from(inner);
                T::exhume(inner_ptr, reader)?;
            }
            Err(ref mut inner) => {
                let inner_ptr : NonNull<E> = From::from(inner);
                E::exhume(inner_ptr, reader)?;
            }
        }
        Some(&mut *self_.as_ptr())
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

unsafe impl<T: Entomb> Entomb for [T] {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) ->  IOResult<()> {
        for element in self { T::entomb(element, write)?; }
        Ok(())
    }

    fn alignment() -> usize {
        <[T; 1]>::alignment()
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for [T] {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This constructs an &[T] to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on slice implementation details.
        let self_len = self_.as_ref().len();
        exhume_slice(self_.as_ptr() as *mut T, self_len, reader)
    }
}

macro_rules! array_abomonate {
    ($size:expr) => (
        unsafe impl<T: Entomb> Entomb for [T; $size] {
            unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) ->  IOResult<()> {
                <[T]>::entomb(&self[..], write)
            }

            fn alignment() -> usize {
                mem::align_of::<Self>().max(T::alignment())
            }
        }

        unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for [T; $size] {
            unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
                exhume_slice(self_.as_ptr() as *mut T, $size, reader)?;
                Some(&mut *self_.as_ptr())
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

unsafe impl<'de> Entomb for &'de str {
    unsafe fn entomb<W: Write>(&self, writer: &mut AlignedWriter<W>) -> IOResult<()> {
        writer.write_slice(self.as_bytes())
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(<[u8; 1]>::alignment())
    }
}
unsafe impl<'de> Exhume<'de> for &'de str {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &str to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on &str implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_str_ref(self_len, reader)?;
        self_.as_ptr().write(s);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<'de> Entomb for &'de mut str {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&str>::entomb(&self.as_ref(), write)
    }

    fn alignment() -> usize {
        <&str>::alignment()
    }
}
unsafe impl<'de> Exhume<'de> for &'de mut str {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &mut str to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on &str implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_str_ref(self_len, reader)?;
        self_.as_ptr().write(s);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl Entomb for String {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&str>::entomb(&self.as_ref(), write)
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(<[u8; 1]>::alignment())
    }
}
unsafe impl<'de> Exhume<'de> for String {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &String to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on String implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_str_ref(self_len, reader)?;
        self_.as_ptr().write(String::from_raw_parts(s.as_mut_ptr(), s.len(), s.len()));
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<'de, T: Entomb + 'de> Entomb for &'de [T] {
    unsafe fn entomb<W: Write>(&self, writer: &mut AlignedWriter<W>) -> IOResult<()> {
        writer.write_slice::<T>(&self[..])?;
        <[T]>::entomb(&self[..], writer)
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(<[T; 1]>::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for &'de [T] {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, bytes: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &[T] to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on slice implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_slice_ref(self_len, bytes)?;
        self_.as_ptr().write(s);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<'de, T: Entomb> Entomb for &'de mut [T] {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&[T]>::entomb(&&self[..], write)
    }

    fn alignment() -> usize {
        <&[T]>::alignment()
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for &'de mut [T] {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, bytes: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &mut [T] to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on slice implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_slice_ref(self_len, bytes)?;
        self_.as_ptr().write(s);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<T: Entomb> Entomb for Vec<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&[T]>::entomb(&&self[..], write)
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(<[T; 1]>::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Vec<T> {
    #[inline]
    unsafe fn exhume(self_: NonNull<Self>, bytes: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        // FIXME: This (briefly) constructs an &Vec<T> to invalid data, which is UB.
        //        I'm not sure if this can be fully resolved without relying on Vec implementation details.
        let self_len = self_.as_ref().len();
        let s = exhume_slice_ref(self_len, bytes)?;
        self_.as_ptr().write(Vec::from_raw_parts(s.as_mut_ptr(), self_len, self_len));
        Some(&mut *self_.as_ptr())
    }
}

// NOTE: While it might be tempting to decouple 'de from the reference target
//       and implement Exhume<'de> for &'target T, the two lifetimes actually
//       have to be exactly the same. Here's proof :
//
//       - Deserialization would produce an &'de &'target T. A reference is
//         only valid if the target is longer-lived, so we need 'target: 'de.
//       - The deserializer will silently patch &'target T into &'de T. This is
//         only safe to do if &'de T : &'target T, so we also need 'de: 'target.
//
//       If 'target must outlive 'de and 'de must outlive 'target, then the two
//       lifetimes actually must be exactly the same. Which kind of makes sense:
//       we start from 'de bytes, and we end up producing references that point
//       into those same bytes.
//
unsafe impl<'de, T: Entomb + 'de> Entomb for &'de T {
    unsafe fn entomb<W: Write>(&self, writer: &mut AlignedWriter<W>) -> IOResult<()> {
        writer.write::<T>(&**self)?;
        T::entomb(&**self, writer)
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(T::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for &'de T {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        let target = exhume_ref(reader)?;
        self_.as_ptr().write(target);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<'de, T: Entomb> Entomb for &'de mut T {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&T>::entomb(&&**self, write)
    }

    fn alignment() -> usize {
        <&T>::alignment()
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for &'de mut T {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        let target = exhume_ref(reader)?;
        self_.as_ptr().write(target);
        Some(&mut *self_.as_ptr())
    }
}

unsafe impl<T: Entomb> Entomb for Box<T> {
    unsafe fn entomb<W: Write>(&self, write: &mut AlignedWriter<W>) -> IOResult<()> {
        <&T>::entomb(&self.as_ref(), write)
    }

    fn alignment() -> usize {
        mem::align_of::<Self>().max(T::alignment())
    }
}
unsafe impl<'de, T: Exhume<'de>> Exhume<'de> for Box<T> {
    unsafe fn exhume(self_: NonNull<Self>, reader: &mut AlignedReader<'de>) -> Option<&'de mut Self> {
        let target = exhume_ref(reader)?;
        self_.as_ptr().write(Box::from_raw(target as *mut _));
        Some(&mut *self_.as_ptr())
    }
}

// Common subset of "exhume" for all [T]-like types
// (I'd gladly move this to [T]::exhume, but building a NonNull<[T]> is currently too difficult)
#[inline]
unsafe fn exhume_slice<'de, T: Exhume<'de>>(
    first_ptr: *mut T,
    length: usize,
    reader: &mut AlignedReader<'de>
) -> Option<&'de mut [T]> {
    for i in 0..length {
        let element_ptr: NonNull<T> = NonNull::new_unchecked(first_ptr.add(i));
        T::exhume(element_ptr, reader)?;
    }
    Some(std::slice::from_raw_parts_mut(first_ptr, length))
}

// Common subset of "exhume" for all &[T]-like types
#[inline]
unsafe fn exhume_slice_ref<'de, T: Exhume<'de>>(
    length: usize,
    reader: &mut AlignedReader<'de>
) -> Option<&'de mut [T]> {
    let first_ptr = reader.read_slice::<T>(length)?.as_ptr();
    exhume_slice(first_ptr, length, reader)
}

// Common subset of "exhume" for all &mut T-like types
unsafe fn exhume_ref<'de, T: Exhume<'de>>(reader: &mut AlignedReader<'de>) -> Option<&'de mut T> {
    let target = reader.read::<T>()?;
    T::exhume(target, reader)
}

// Common subset of "exhume" for all &str-like types
unsafe fn exhume_str_ref<'de>(length: usize, reader: &mut AlignedReader<'de>) -> Option<&'de mut str> {
    let bytes = exhume_slice_ref::<u8>(length, reader)?;
    Some(std::str::from_utf8_unchecked_mut(bytes))
}

mod network {
    use super::{Entomb, Exhume};
    use std::net::{SocketAddr, SocketAddrV4, SocketAddrV6, IpAddr, Ipv4Addr, Ipv6Addr};

    unsafe impl Entomb for IpAddr { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for IpAddr {}
    unsafe impl Entomb for Ipv4Addr { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for Ipv4Addr {}
    unsafe impl Entomb for Ipv6Addr { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for Ipv6Addr {}

    unsafe impl Entomb for SocketAddr { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for SocketAddr {}
    unsafe impl Entomb for SocketAddrV4 { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for SocketAddrV4 {}
    unsafe impl Entomb for SocketAddrV6 { fn alignment() -> usize { std::mem::align_of::<Self>() } }
    unsafe impl Exhume<'_> for SocketAddrV6 {}
}
