
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use super::{Abomonation, decode};

/// A type wrapping owned decoded abomonated data.
///
/// This type ensures that decoding and pointer correction has already happened.
/// It provides a way to move the deserialized data around, while keeping
/// on-demand access to it via the `as_ref()` method.
///
/// As an extra convenience, `Deref<Target=T>` is also implemented if T does
/// not contain references. Unfortunately, this trait cannot be safely
/// implemented when T does contain references.
///
/// #Safety
///
/// The safety of this type, and in particular of access to the deserialized
/// data, relies on the owned bytes not being externally mutated after the
/// `Abomonated` is constructed. You could imagine a new type implementing
/// `DerefMut` as required, but which also retains the ability (e.g. through
/// `RefCell`) to mutate the bytes. This would be very bad, but seems hard to
/// prevent in the type system. Please don't do this.
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

impl<'s, 't, T, S> Abomonated<T, S>
    where S: DerefMut<Target=[u8]> + 's,
          T: Abomonation<'t>,
          's: 't
{
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
        // Fix type `T`'s inner pointers. Will return `None` on failure.
        //
        // FIXME: `slice::from_raw_parts_mut` is used to work around the borrow
        //        checker marking `bytes` as forever borrowed if `&mut bytes` is
        //        directly passed as input to `decode()`. But that is itself a
        //        byproduct of the API contract specified by the `where` clause
        //        above, which allows S to be `&'t mut [u8]` (and therefore
        //        require such a perpetual borrow) in the worst case.
        //
        //        A different API contract might allow us to achieve the same
        //        result without resorting to such evil unsafe tricks.
        //
        decode::<T>(std::slice::from_raw_parts_mut(bytes.as_mut_ptr(),
                                                   bytes.len()))?;

        // Build the Abomonated structure
        Some(Abomonated {
            phantom: PhantomData,
            decoded: bytes,
        })
    }
}

impl<'t, T, S> Abomonated<T, S>
    where S: DerefMut<Target=[u8]>,
          T: Abomonation<'t>
{
    /// Get a read-only view on the deserialized bytes
    pub fn as_bytes(&self) -> &[u8] {
        &self.decoded
    }

    /// Get a read-only view on the deserialized data
    //
    // NOTE: This method can be safely used even if type T contains references,
    //       because it makes sure that the borrow of `self` lasts long enough
    //       to encompass the lifetime of these references.
    //
    //       Otherwise, it would be possible to extract an `&'static Something`
    //       from a short-lived borrow of a `Box<[u8]>`, then drop the `Box`,
    //       and end up with a dangling reference.
    //
    pub fn as_ref<'a: 't>(&'a self) -> &'a T {
        unsafe { &*(self.decoded.as_ptr() as *const T) }
    }
}

// NOTE: The lifetime constraint that was applied to `as_ref()` cannot be
//       applied to a `Deref` implementation. Therefore, `Deref` can only be
//       used on types T which do not contain references, as enforced by the
//       higher-ranked trait bound below.
impl<T, S> Deref for Abomonated<T, S>
    where S: DerefMut<Target=[u8]>,
          for<'t> T: Abomonation<'t>,
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}
