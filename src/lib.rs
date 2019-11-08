//!
//!Types for constructing free algebras over sets.
//!
//!# What even is a "Free Algebra"?
//!
//!In the context of this crate, the term "Algebra" refers to the general branch of mathematical
//!constructions involving arithmetic operations, and the term "Free" refers to the nature of those
//!operations. In particular, a "free" operation is one that is made with as little restriction
//!as possible without violating the algebraic rules that are desired.
//!
//!Hence, in general, the procedure to make such a "free" construction is to start with some type `T`
//!(and it could really be any type), and some set of algebraic rules, and then simply apply them
//!to elements of `T` as if they were a variable or symbol.
//!
//!As abstract as that sounds, there is actually a prime example of this already in the standard
//!library, the [`Vec<T>`](Vec)! If we start with some type `T`, assert that multiplication be associative,
//!and start multiplying elements as variables, the result is exactly the same as if we took
//![`Vec<T>`](Vec) and implemented concatenation as [multiplication](Mul) and the empty list as
//![`1`](One) In fact, the type [`FreeMonoid<T>`](FreeMonoid) in this crate is *precisely* that.
//!
//!```
//!use maths_traits::algebra::One;
//!use free_algebra::FreeMonoid;
//!
//!let x: FreeMonoid<char> = FreeMonoid::one();
//!let y = FreeMonoid::one() * 'a' * 'b';
//!let z = FreeMonoid::one() * 'c' * 'd';
//!
//!assert_eq!(x, vec![]);
//!assert_eq!(y, vec!['a', 'b']);
//!assert_eq!(z, vec!['c', 'd']);
//!assert_eq!(&y * &z, vec!['a', 'b', 'c', 'd']);
//!assert_eq!(&z * &y, vec!['c', 'd', 'a', 'b']);
//!
//!```
//!
//!In addition to this, however, there are a number of other constructions you can get by changing
//!what types are used, which operations are considered, and what rules are followed. Examples include:
//! * [`FreeModule<R,T>`](FreeModule): results from requiring that elements of `T` can be added
//!   together commutatively and associatively and can be multiplied distributively by the scalar
//!   type `R`
//! * [`FreeAlgebra<R,T>`](FreeAlgebra): This is the same as [FreeModule], except that we let `T`
//!   multiply distributively with itself freely similarly as with [FreeMonoid]
//! * Polynomials: A [FreeAlgebra], but where multiplication between `T`'s is commutative and associative
//! * Clifford algebra: A [FreeAlgebra], but where multiplication is associative and
//!   an element times itself results in a scalars
//! * Complex numbers: Results from when `T` includes `1` and `i` and multiplies accordingly
//! * Quaternions: Same as for Complex numbers, but with more imaginary units
//!
//!# Crate structures
//!
//!This crate consists of the following:
//! * Two main structures for doing the free-arithmetic over some type
//! * Traits for specifying the rules for arithmetic
//! * Type aliases for particular combinations of construction and rules
//!
//!Specifically:
//! * [MonoidalString] constructs free-multiplying structures over a type `T` using an order-dependent
//!   internal representation with a [`Vec<T>`](Vec) and determines its multiplication rule using an
//!   implementor of [MonoidRule]. Aliases of this struct include [FreeMonoid] and [FreeGroup]
//! * [ModuleString] constructs types consisting of terms of type `T` with scalars from
//!   some additive type `R` stored with an order independent [HashMap]. This grants all [ModuleString]'s
//!   an addition operation from adding the coeffients of like terms, but a free-multiplication can
//!   be added with an optional [AlgebraRule]. Aliases of this struct include [FreeModule] and [FreeAlgebra]
//!
//!For more information, see the respective structs
//!
//!

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
use std::fmt::{Display, Formatter};

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

pub(self) trait IsZero: Sized {
    fn _is_zero(&self) -> bool;
    fn _zero() -> Option<Self>;
}
impl<T> IsZero for T {
    default fn _is_zero(&self) -> bool { false }
    default fn _zero() -> Option<Self> {None}
}
impl<T:Zero> IsZero for T {
    default fn _is_zero(&self) -> bool { self.is_zero() }
    default fn _zero() -> Option<Self> { Some(Self::zero()) }
}

pub use self::specifics::*;
mod specifics;

pub mod monoid;
pub mod module;
