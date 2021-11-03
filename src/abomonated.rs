#![cfg_attr(feature = "no_std", no_std)]

#[cfg(not(feature="no_std"))]
use {
    std::mem::transmute,
    std::marker::PhantomData,
    std::ops::{Deref, DerefMut},
};

#[cfg(feature="no_std")]
use {
    core::mem::transmute,
    core::marker::PhantomData,
    core::ops::{Deref, DerefMut},
};

use super::{Abomonation, decode};

/// A type wrapping owned decoded abomonated data.
///
/// This type ensures that decoding and pointer correction has already happened,
/// and implements `Deref<Target=T>` using a pointer cast (transmute).
///
/// #Safety
///
/// The safety of this type, and in particular its `transute` implementation of
/// the `Deref` trait, relies on the owned bytes not being externally mutated
/// once provided. You could imagine a new type implementing `DerefMut` as required,
/// but which also retains the ability (e.g. through `RefCell`) to mutate the bytes.
/// This would be very bad, but seems hard to prevent in the type system. Please
/// don't do this.
///
/// You must also use a type `S` whose bytes have a fixed location in memory.
/// Otherwise moving an instance of `Abomonated<T, S>` may invalidate decoded
/// pointers, and everything goes badly.
///
/// #Examples
///
/// ```
/// use std::ops::Deref;
/// use abomonation::{encode, decode};
/// use abomonation::abomonated::Abomonated;
///
/// // create some test data out of abomonation-approved types
/// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
///                         .collect::<Vec<_>>();
///
/// // encode a Vec<(u64, String)> into a Vec<u8>
/// let mut bytes = Vec::new();
/// unsafe { encode(&vector, &mut bytes); }
///
/// // attempt to decode `bytes` into a `&Vec<(u64, String)>`.
/// let maybe_decoded = unsafe { Abomonated::<Vec<(u64, String)>,_>::new(bytes) };
///
/// if let Some(decoded) = maybe_decoded {
///     // each `deref()` call is now just a pointer cast.
///     assert!(decoded.deref() == &vector);
/// }
/// else {
///     panic!("failed to decode");
/// }
/// ```
pub struct Abomonated<T, S: DerefMut<Target=[u8]>> {
    phantom: PhantomData<T>,
    decoded: S,
}

impl<T: Abomonation, S: DerefMut<Target=[u8]>> Abomonated<T, S> {

    /// Attempts to create decoded data from owned mutable bytes.
    ///
    /// This method will return `None` if it is unable to decode the data with
    /// type `T`.
    ///
    /// #Examples
    ///
    /// ```
    /// use std::ops::Deref;
    /// use abomonation::{encode, decode};
    /// use abomonation::abomonated::Abomonated;
    ///
    /// // create some test data out of abomonation-approved types
    /// let vector = (0..256u64).map(|i| (i, format!("{}", i)))
    ///                         .collect::<Vec<_>>();
    ///
    /// // encode a Vec<(u64, String)> into a Vec<u8>
    /// let mut bytes = Vec::new();
    /// unsafe { encode(&vector, &mut bytes); }
    ///
    /// // attempt to decode `bytes` into a `&Vec<(u64, String)>`.
    /// let maybe_decoded = unsafe { Abomonated::<Vec<(u64, String)>,_>::new(bytes) };
    ///
    /// if let Some(decoded) = maybe_decoded {
    ///     // each `deref()` call is now just a pointer cast.
    ///     assert!(decoded.deref() == &vector);
    /// }
    /// else {
    ///     panic!("failed to decode");
    /// }
    /// ```
    ///
    /// #Safety
    ///
    /// The type `S` must have its bytes at a fixed location, which will
    /// not change if the `bytes: S` instance is moved. Good examples are
    /// `Vec<u8>` whereas bad examples are `[u8; 16]`.
    pub unsafe fn new(mut bytes: S) -> Option<Self> {

        // performs the underlying pointer correction, indicates success.
        let decoded = decode::<T>(bytes.deref_mut()).is_some();

        if decoded {
            Some(Abomonated {
                phantom: PhantomData,
                decoded: bytes,
            })
        }
        else {
            None
        }
    }
}

impl<T, S: DerefMut<Target=[u8]>> Abomonated<T, S> {
    pub fn as_bytes(&self) -> &[u8] {
        &self.decoded
    }
}


impl<T, S: DerefMut<Target=[u8]>> Deref for Abomonated<T, S> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        let result: &T = unsafe { transmute(self.decoded.get_unchecked(0)) };
        result
    }
}
