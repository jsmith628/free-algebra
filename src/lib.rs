#![feature(specialization)]

extern crate maths_traits;

pub use self::monoid::*;
pub use self::module::*;

macro_rules! from_assign {

    (impl<$($T:ident),*> $Trait:ident<$RHS:ident>.$fun:ident for $ty:ident<$($U:ident),*> with $op:tt $($where:tt)*) => {
        impl<$($T),*> $Trait<$RHS> for $ty<$($U),*> $($where)* {
            type Output = Self;
            #[inline] fn $fun(mut self, rhs:$RHS) -> Self {self $op rhs; self}
        }
    }

}

pub mod monoid;
pub mod module;
