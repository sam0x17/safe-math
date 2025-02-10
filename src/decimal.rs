use core::{cmp::Ordering, ops::*, str::FromStr};
use rug::{
    integer::ParseIntegerError,
    ops::{NegAssign, Pow},
    Integer,
};

#[derive(Clone, Debug, Eq, Ord, Hash, Default)]
#[repr(transparent)]
pub struct SafeDec<const D: usize>(Integer);

impl<const D: usize> SafeDec<D> {
    pub const ZERO: SafeDec<D> = SafeDec::<D>(Integer::ZERO);
    pub const BASE: u128 = 10u128.pow(D as u32);

    #[inline(always)]
    pub fn from_float(value: impl Into<f64>) -> SafeDec<D> {
        let value = value.into();
        todo!()
    }

    #[inline(always)]
    pub const fn from_raw(value: Integer) -> SafeDec<D> {
        SafeDec(value)
    }

    #[inline(always)]
    pub const fn is_negative(&self) -> bool {
        self.0.is_negative()
    }

    #[inline(always)]
    pub const fn is_even(&self) -> bool {
        self.0.is_even()
    }

    #[inline(always)]
    pub const fn is_odd(&self) -> bool {
        self.0.is_odd()
    }

    #[inline(always)]
    pub const fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    #[inline(always)]
    pub fn abs(self) -> SafeDec<D> {
        SafeDec(self.0.abs())
    }

    #[inline(always)]
    pub fn pow(self, exp: u32) -> SafeDec<D> {
        SafeDec(self.0.pow(exp))
    }
}

impl<const D: usize> FromStr for SafeDec<D> {
    type Err = ParseIntegerError;

    #[inline(always)]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(SafeDec(Integer::from_str(s)?))
    }
}

impl<const D: usize> Neg for SafeDec<D> {
    type Output = SafeDec<D>;

    #[inline(always)]
    fn neg(self) -> SafeDec<D> {
        SafeDec(-self.0)
    }
}

impl<const D: usize> NegAssign for SafeDec<D> {
    #[inline(always)]
    fn neg_assign(&mut self) {
        self.0.neg_assign();
    }
}

macro_rules! impl_binary_op {
    ($trait:ident, $method:ident) => {
        impl<const D: usize> $trait for SafeDec<D> {
            type Output = SafeDec<D>;

            #[inline(always)]
            fn $method(self, other: SafeDec<D>) -> SafeDec<D> {
                SafeDec(self.0.$method(other.0))
            }
        }

        impl<const D: usize> $trait<&SafeDec<D>> for &SafeDec<D> {
            type Output = SafeDec<D>;

            #[inline(always)]
            fn $method(self, other: &SafeDec<D>) -> SafeDec<D> {
                SafeDec(self.0.clone().$method(&other.0))
            }
        }

        impl<const D: usize> $trait<&SafeDec<D>> for SafeDec<D> {
            type Output = SafeDec<D>;

            #[inline(always)]
            fn $method(self, other: &SafeDec<D>) -> SafeDec<D> {
                SafeDec(self.0.$method(&other.0))
            }
        }

        impl<const D: usize> $trait<SafeDec<D>> for &SafeDec<D> {
            type Output = SafeDec<D>;

            #[inline(always)]
            fn $method(self, other: SafeDec<D>) -> SafeDec<D> {
                SafeDec(self.0.clone().$method(other.0))
            }
        }
    };
}

macro_rules! impl_assign_op {
    ($trait:ident, $method:ident) => {
        impl<const D: usize> $trait for SafeDec<D> {
            #[inline(always)]
            fn $method(&mut self, other: SafeDec<D>) {
                self.0.$method(other.0);
            }
        }

        impl<const D: usize> $trait<&SafeDec<D>> for SafeDec<D> {
            #[inline(always)]
            fn $method(&mut self, other: &SafeDec<D>) {
                self.0.$method(&other.0);
            }
        }
    };
}

impl_binary_op!(Add, add);
impl_binary_op!(Sub, sub);
impl_binary_op!(Mul, mul);
impl_binary_op!(Rem, rem);
impl_binary_op!(BitAnd, bitand);
impl_binary_op!(BitOr, bitor);
impl_binary_op!(BitXor, bitxor);
impl_assign_op!(AddAssign, add_assign);
impl_assign_op!(SubAssign, sub_assign);
impl_assign_op!(MulAssign, mul_assign);
impl_assign_op!(RemAssign, rem_assign);
impl_assign_op!(BitAndAssign, bitand_assign);
impl_assign_op!(BitOrAssign, bitor_assign);
impl_assign_op!(BitXorAssign, bitxor_assign);

impl<const D: usize> Div for SafeDec<D> {
    type Output = Option<SafeDec<D>>;

    #[inline(always)]
    fn div(self, other: SafeDec<D>) -> Option<SafeDec<D>> {
        if other.0.is_zero() {
            None
        } else {
            Some(SafeDec(self.0.div(other.0)))
        }
    }
}

impl<const D: usize> Div<&SafeDec<D>> for SafeDec<D> {
    type Output = Option<SafeDec<D>>;

    #[inline(always)]
    fn div(self, other: &SafeDec<D>) -> Option<SafeDec<D>> {
        if other.0.is_zero() {
            None
        } else {
            Some(SafeDec(self.0.div(&other.0)))
        }
    }
}

impl<const D: usize> Div<SafeDec<D>> for &SafeDec<D> {
    type Output = Option<SafeDec<D>>;

    #[inline(always)]
    fn div(self, other: SafeDec<D>) -> Option<SafeDec<D>> {
        if other.0.is_zero() {
            None
        } else {
            Some(SafeDec(self.0.clone().div(other.0)))
        }
    }
}

impl<const D: usize, T: PartialEq<Integer>> PartialEq<T> for SafeDec<D> {
    #[inline(always)]
    fn eq(&self, other: &T) -> bool {
        *other == self.0
    }
}

impl<const D: usize, T: PartialOrd<Integer>> PartialOrd<T> for SafeDec<D> {
    #[inline(always)]
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        match other.partial_cmp(&self.0) {
            Some(Ordering::Less) => Some(Ordering::Greater),
            Some(Ordering::Greater) => Some(Ordering::Less),
            equal => equal,
        }
    }
}

#[test]
fn general() {}
