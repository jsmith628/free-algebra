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

///Implements an operator overload using the assign variant
macro_rules! from_assign {

    (impl<$($T:ident),*> $Trait:ident<$RHS:ident>.$fun:ident for $ty:ident<$($U:ident),*> with $op:tt $($where:tt)*) => {
        impl<$($T),*> $Trait<$RHS> for $ty<$($U),*> $($where)* {
            type Output = Self;
            #[inline] fn $fun(mut self, rhs:$RHS) -> Self {self $op rhs; self}
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
