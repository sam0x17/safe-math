use crate::u64ptr::U63OrPtr;

#[repr(C)]
pub struct Decimal<const D: usize> {
    data: U63OrPtr,
}
