#![feature(specialization)]
#![feature(marker_trait_attr)]

#[macro_use] extern crate derivative;
extern crate num_traits;
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

mod monoid;
mod module;
