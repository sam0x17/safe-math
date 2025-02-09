extern crate alloc;
use alloc::alloc::dealloc;
use alloc::boxed::Box;
use core::ptr::NonNull;

pub const MAX_U63: u64 = (1 << 63) - 1;

/// An unsafe type that stores either a 63-bit integer or a pointer with a size.
///
/// # Safety
/// This type contains a `NonNull<u8>`, which requires careful handling to avoid
/// undefined behavior. Users must ensure that pointers stored in this type
/// remain valid for the duration of their use.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct U63OrPtr {
    data: u64,
}

impl U63OrPtr {
    /// Checks if the pointer was dynamically allocated
    pub const fn is_allocated(&self) -> bool {
        (self.data & (1 << 62)) != 0
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum U63OrPtrError {
    ValueTooLarge,
    InvalidPointer,
    SizeTooLarge,
}

/// Represents the expanded version of U63OrPtr for safe inspection
#[derive(Debug, PartialEq)]
pub enum U63OrPtrExpanded {
    U64(u64),
    Ptr(NonNull<u8>, usize),
}

impl U63OrPtr {
    const DISCRIMINANT: u64 = 1 << 63; // First bit is the discriminant
    const PTR_MASK: u64 = (1 << 48) - 1; // 48-bit address mask
    const SIZE_SHIFT: u64 = 48;
    const SIZE_MASK: u64 = (1 << 15) - 1; // 15-bit size mask

    /// Create a new U63 value
    pub const fn from_u63(value: u64) -> Result<Self, U63OrPtrError> {
        if value >= Self::DISCRIMINANT {
            Err(U63OrPtrError::ValueTooLarge)
        } else {
            Ok(Self { data: value })
        }
    }

    /// Create a new pointer with a size
    ///
    /// # Safety
    /// The caller must ensure that the pointer is properly aligned, non-null,
    /// and that the size fits within 15 bits.
    pub unsafe fn from_ptr(ptr: NonNull<u8>, size: u16) -> Result<Self, U63OrPtrError> {
        let addr = ptr.as_ptr() as u64;
        if addr & !Self::PTR_MASK != 0 {
            return Err(U63OrPtrError::InvalidPointer);
        }
        if size as u64 > Self::SIZE_MASK {
            return Err(U63OrPtrError::SizeTooLarge);
        }
        Ok(Self {
            data: Self::DISCRIMINANT
                | addr
                | ((size as u64 & Self::SIZE_MASK) << Self::SIZE_SHIFT)
                | (1 << 62),
        })
    }

    /// Create a new [`U63OrPtr`]` from the specified value by heap allocating `val`.
    pub fn from_val<T: Sized>(val: T) -> Self {
        const { assert!(size_of::<T>() <= 32000) }
        let bx = Box::new(val);
        let ptr: *mut u8 = Box::leak(bx) as *mut T as *mut u8;
        let Some(ptr_non) = NonNull::new(ptr) else {
            unreachable!("pointer is non-null")
        };
        let size = core::mem::size_of::<T>() as u16;
        let Ok(s) = (unsafe { Self::from_ptr(ptr_non, size) }) else {
            unreachable!("const assertion prevents this")
        };
        s
    }

    /// Check if this is a u63 value
    pub const fn is_u63(&self) -> bool {
        (self.data & Self::DISCRIMINANT) == 0
    }

    /// Check if this is a pointer
    pub const fn is_ptr(&self) -> bool {
        !self.is_u63()
    }

    /// Extract the expanded representation
    ///
    /// # Safety
    /// This function constructs a `NonNull<u8>` from a raw pointer, which assumes
    /// that the pointer was originally valid when stored.
    pub fn expand(&self) -> U63OrPtrExpanded {
        if self.is_u63() {
            U63OrPtrExpanded::U64(self.data)
        } else {
            let addr = self.data & Self::PTR_MASK;
            let size = (((self.data >> Self::SIZE_SHIFT) & Self::SIZE_MASK)
                & !(1 << (62 - Self::SIZE_SHIFT))) as usize;
            let non_null_ptr =
                NonNull::new(addr as *mut u8).expect("Invalid pointer stored in U63OrPtr");
            U63OrPtrExpanded::Ptr(non_null_ptr, size)
        }
    }
}

impl Drop for U63OrPtr {
    fn drop(&mut self) {
        if self.is_ptr() && self.is_allocated() {
            unsafe {
                let addr = self.data & Self::PTR_MASK;
                let non_null_ptr =
                    NonNull::new(addr as *mut u8).expect("Invalid pointer stored in U63OrPtr");
                use core::alloc::Layout;
                let layout = Layout::from_size_align(
                    ((self.data >> Self::SIZE_SHIFT) & Self::SIZE_MASK) as usize,
                    8,
                )
                .unwrap();
                dealloc(non_null_ptr.as_ptr(), layout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u63() {
        let mut i = 0;
        const INC: u64 = MAX_U63 / 1_000_000;
        loop {
            let val = U63OrPtr::from_u63(i).unwrap();
            assert!(val.is_u63());
            assert_eq!(val.expand(), U63OrPtrExpanded::U64(i));
            i += INC;
            if i >= MAX_U63 {
                break;
            }
        }
    }

    #[test]
    fn test_u63_too_large() {
        assert_eq!(
            U63OrPtr::from_u63(1 << 63),
            Err(U63OrPtrError::ValueTooLarge)
        );
    }

    #[test]
    fn test_ptr() {
        let mut value: u128 = 0;
        const INC: u128 = u128::MAX / 10_000;
        loop {
            let mut bx = Box::new(value);
            let ptr: *mut u8 = &mut *bx as *mut u128 as *mut u8;
            core::mem::forget(bx);
            let ptr = NonNull::new(ptr).unwrap();

            let val = unsafe { U63OrPtr::from_ptr(ptr, size_of::<u128>() as u16).unwrap() };
            assert!(val.is_ptr());

            if let U63OrPtrExpanded::Ptr(expanded_ptr, expanded_size) = val.expand() {
                assert_eq!(expanded_size, size_of::<u128>());
                assert_eq!(expanded_ptr, ptr);

                // Read back and assert correctness
                let stored_value = unsafe { *(expanded_ptr.as_ptr() as *const u128) };
                assert_eq!(stored_value, value);
            } else {
                panic!("Expected a pointer variant");
            }

            if u128::MAX - INC < value {
                break;
            }

            value += INC;
        }
    }
}
