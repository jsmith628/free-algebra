#![feature(specialization)]
#![feature(marker_trait_attr)]
#![feature(never_type)]

#[macro_use] extern crate derivative;
extern crate num_traits;
extern crate maths_traits;

pub use self::monoid::*;
pub use self::module::*;

use maths_traits::algebra::*;

use num_traits::Pow;

use std::marker::PhantomData;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;

use std::iter::*;

macro_rules! impl_arith {

    (impl<$($T:ident),*> $Trait:ident.$fun:ident with $TraitAssign:ident.$fun_assign:ident for $ty:ty where $($where:tt)*) => {

        //impl of an op using its assign variant
        impl<RHS, $($T),*> $Trait<RHS> for $ty where $($where)*, Self:$TraitAssign<RHS> {
            type Output = Self;
            #[inline] fn $fun(mut self, rhs:RHS) -> Self {self.$fun_assign(rhs); self}
        }

        //impl of an op on a reference
        impl<'a, RHS, $($T),*> $Trait<RHS> for &'a $ty where $($where)*, $ty:Clone+$Trait<RHS> {
            type Output = <$ty as $Trait<RHS>>::Output;
            #[inline] fn $fun(self, rhs:RHS) -> Self::Output {(*self).clone().$fun(rhs)}
        }
    };

    (impl<$($T:ident),*> $TraitAssign:ident<&$RHS:ident>.$fun_assign:ident for $ty:ty where $($where:tt)*) => {

        //impl of an op with a reference
        impl<'a, $($T),*> $TraitAssign<&'a $RHS> for $ty where $($where)*, Self:$TraitAssign<$RHS>, $RHS:Clone {
            #[inline] fn $fun_assign(&mut self, rhs:&'a $RHS) {self.$fun_assign((*rhs).clone())}
        }

    }

}

pub(self) trait IsZero { fn _is_zero(&self) -> bool; }
impl<T> IsZero for T { default fn _is_zero(&self) -> bool { false } }
impl<T:Zero> IsZero for T { default fn _is_zero(&self) -> bool { self.is_zero() } }

pub use self::specifics::*;
mod specifics;

pub mod monoid;
pub mod module;
