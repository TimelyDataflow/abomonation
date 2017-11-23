use ::std::mem::size_of;
use super::Abomonation;

/// Analogue of `unsafe_abomonate` to additionally implement `AbomonationSize`.
#[macro_export]
macro_rules! unsafe_abomonate_size {
    ($t:ty) => { 
        impl Abomonation for $t { } 
        impl AbomonationSize for $t { }
    };
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
        impl AbomonationSize for $t {
            #[inline] fn extent(&self) -> usize {
                let mut size = 0;
                $( size += self.$field.extent(); )*
                size
            }
        }
    };
}

/// Sizing information for typed data in number of bytes required.a
pub trait AbomonationSize: Abomonation + ::std::marker::Sized {
    /// Reports the number of further bytes required to entomb `self`.
    #[inline(always)] fn extent(&self) -> usize { 0 }

    /// Reports the number of bytes required to encode `self`.
    #[inline(always)]
    fn measure(&self) -> usize {
        size_of::<Self>() + self.extent()
    }
}

impl AbomonationSize for u8 { }
impl AbomonationSize for u16 { }
impl AbomonationSize for u32 { }
impl AbomonationSize for u64 { }
impl AbomonationSize for usize { }

impl AbomonationSize for i8 { }
impl AbomonationSize for i16 { }
impl AbomonationSize for i32 { }
impl AbomonationSize for i64 { }
impl AbomonationSize for isize { }

impl AbomonationSize for f32 { }
impl AbomonationSize for f64 { }

impl AbomonationSize for bool { }
impl AbomonationSize for () { }

impl AbomonationSize for char { }

impl<T> AbomonationSize for ::std::marker::PhantomData<T> {}

impl<T: AbomonationSize> AbomonationSize for Option<T> {
    #[inline] fn extent(&self) -> usize {
        self.as_ref().map(|inner| inner.extent()).unwrap_or(0)
    }
}

impl<T: AbomonationSize, E: AbomonationSize> AbomonationSize for Result<T, E> {
    #[inline] fn extent(&self) -> usize {
        match self {
            &Ok(ref inner) => inner.extent(),
            &Err(ref inner) => inner.extent(),
        }
    }
}

impl AbomonationSize for String {
    #[inline] fn extent(&self) -> usize {
        self.len()
    }
}

impl<T: AbomonationSize> AbomonationSize for Vec<T> {
    #[inline] fn extent(&self) -> usize {
        let mut sum = size_of::<T>() * self.len();
        // let mut sum = typed_to_bytes(&self[..]).len();
        for element in self.iter() {
            sum += element.extent();
        }
        sum
    }
}

impl<T: AbomonationSize> AbomonationSize for Box<T> {
    #[inline] fn extent(&self) -> usize {
        size_of::<T>() + (&**self).extent()
        // ::std::slice::from_raw_parts::<u8>(::std::mem::transmute(&**self), size_of::<T>()).len() + (&**self).extent()
        // size_of::<Self>() + (&**self).extent()
    }
}
