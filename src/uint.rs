use crate::u64ptr::{U63OrPtr, MAX_U63};

#[repr(C)]
pub struct UInt {
    data: U63OrPtr,
}

impl UInt {}

impl From<u8> for UInt {
    fn from(val: u8) -> Self {
        Self {
            data: U63OrPtr::from_u63(val as u64).expect("u8 fits in 63 bits"),
        }
    }
}

impl From<u16> for UInt {
    fn from(val: u16) -> Self {
        Self {
            data: U63OrPtr::from_u63(val as u64).expect("u16 fits in 63 bits"),
        }
    }
}

impl From<u32> for UInt {
    fn from(val: u32) -> Self {
        Self {
            data: U63OrPtr::from_u63(val as u64).expect("u32 fits in 63 bits"),
        }
    }
}

impl From<u64> for UInt {
    fn from(val: u64) -> Self {
        if val > MAX_U63 {
            todo!()
        } else {
            Self {
                data: U63OrPtr::from_u63(val).expect("fits in 63 bits"),
            }
        }
    }
}
