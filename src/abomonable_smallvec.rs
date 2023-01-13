use crate::Abomonation;
use smallvec::{Array, SmallVec};
use std::io::Result as IOResult;
use std::io::Write;
use std::mem;

impl<A: Array> Abomonation for SmallVec<A>
where
    A::Item: Abomonation,
{
    #[inline]
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        if self.spilled() {
            write.write_all(crate::typed_to_bytes(&self[..]))?;
        }
        for element in self.iter() {
            element.entomb(write)?;
        }
        Ok(())
    }

    #[inline]
    unsafe fn exhume<'a, 'b>(&'a mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        // extract memory from bytes to back our smallvec
        let binary_len = if self.spilled() {
            self.len() * mem::size_of::<A::Item>()
        } else {
            0
        };
        if binary_len > bytes.len() {
            None
        } else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            if self.spilled() {
                let slice =
                    std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut A::Item, self.len());
                // If the vector has spilled but then been truncated down to
                // less than the capacity, we must lie about the capacity to
                // maintain the spilled invariant.  This is ok, as the
                // exhumed smallvec is read-only.
                let capacity = self.inline_size().saturating_add(1).max(self.len());
                std::ptr::write(
                    self,
                    SmallVec::from_raw_parts(slice.as_mut_ptr(), self.len(), capacity),
                );
            }
            for element in self.iter_mut() {
                let temp = rest; // temp variable explains lifetimes (mysterious!)
                rest = element.exhume(temp)?;
            }
            Some(rest)
        }
    }

    #[inline]
    fn extent(&self) -> usize {
        let mut sum = 0;
        if self.spilled() {
            sum += mem::size_of::<A::Item>() * self.len();
        }
        for element in self.iter() {
            sum += element.extent();
        }
        sum
    }
}

#[cfg(test)]
mod tests {
    use crate::{decode, encode, measure, Abomonation};
    use smallvec::{smallvec, SmallVec};

    fn _test_pass<T: Abomonation + Eq>(record: T) {
        let mut bytes = Vec::new();
        unsafe {
            encode(&record, &mut bytes).unwrap();
        }
        {
            let (result, rest) = unsafe { decode::<T>(&mut bytes[..]) }.unwrap();
            assert!(&record == result);
            assert!(rest.len() == 0);
        }
    }

    fn _test_fail<T: Abomonation>(record: T) {
        let mut bytes = Vec::new();
        unsafe {
            encode(&record, &mut bytes).unwrap();
        }
        bytes.pop();
        assert!(unsafe { decode::<T>(&mut bytes[..]) }.is_none());
    }

    fn _test_size<T: Abomonation>(record: T) {
        let mut bytes = Vec::new();
        unsafe {
            encode(&record, &mut bytes).unwrap();
        }
        assert_eq!(bytes.len(), measure(&record));
    }

    #[test]
    fn test_smallvec_empty_pass() {
        _test_pass::<SmallVec<[(u64, String); 8]>>(smallvec![])
    }

    #[test]
    fn test_smallvec_unspilled_pass() {
        _test_pass::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 3])
    }

    #[test]
    fn test_smallvec_spilled_pass() {
        _test_pass::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 17])
    }

    #[test]
    fn test_smallvec_truncated_pass() {
        let mut v: SmallVec<[(u64, String); 8]> = smallvec![(0u64, format!("meow")); 17];
        v.truncate(5);
        _test_pass(v)
    }

    #[test]
    fn test_smallvec_zst_pass() {
        _test_pass::<SmallVec<[(); 8]>>(smallvec![(); 17])
    }

    #[test]
    fn test_smallvec_empty_fail() {
        _test_fail::<SmallVec<[(u64, String); 8]>>(smallvec![])
    }

    #[test]
    fn test_smallvec_unspilled_fail() {
        _test_fail::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 3])
    }

    #[test]
    fn test_smallvec_spilled_fail() {
        _test_fail::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 17])
    }

    #[test]
    fn test_smallvec_truncated_fail() {
        let mut v: SmallVec<[(u64, String); 8]> = smallvec![(0u64, format!("meow")); 17];
        v.truncate(5);
        _test_fail(v)
    }

    #[test]
    fn test_smallvec_zst_fail() {
        _test_fail::<SmallVec<[(); 8]>>(smallvec![(); 17])
    }

    #[test]
    fn test_smallvec_empty_size() {
        _test_size::<SmallVec<[(u64, String); 8]>>(smallvec![])
    }

    #[test]
    fn test_smallvec_unspilled_size() {
        _test_size::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 3])
    }

    #[test]
    fn test_smallvec_spilled_size() {
        _test_size::<SmallVec<[(u64, String); 8]>>(smallvec![(0u64, format!("meow")); 17])
    }

    #[test]
    fn test_smallvec_truncated_size() {
        let mut v: SmallVec<[(u64, String); 8]> = smallvec![(0u64, format!("meow")); 17];
        v.truncate(5);
        _test_size(v)
    }

    #[test]
    fn test_smallvec_zst_size() {
        _test_size::<SmallVec<[(); 8]>>(smallvec![(); 17])
    }
}
