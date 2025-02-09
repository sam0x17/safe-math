#[repr(C)]
pub enum HeapInt {
    U120([u8; 15]),
    Ptr { len: [u8; 7], ptr: *mut u8 },
}

impl HeapInt {
    pub const fn from_u8(val: u8) -> Self {
        HeapInt::U120([val; 15])
    }
}
