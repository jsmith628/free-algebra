
use num_traits::Pow;
use maths_traits::algebra::*;

use std::marker::PhantomData;
use std::ops::Index;
use std::borrow::Borrow;
use std::iter::*;

#[derive(Derivative)]
#[derivative(Clone(clone_from="true"))]
#[derivative(Default(bound=""))]
#[derivative(PartialEq, Eq, Hash)]
#[derivative(Debug="transparent")]
pub struct MonoidalString<C,A:?Sized,M:?Sized> {
    #[derivative(Default(value="Vec::with_capacity(0)"))]
    string: Vec<C>,

    #[derivative(PartialEq="ignore", Hash="ignore")]
    #[derivative(Debug="ignore")]
    rules: PhantomData<(Box<A>,Box<M>)>
}

impl<C,A:?Sized,M:?Sized> From<C> for MonoidalString<C,A,M> {
    #[inline] fn from(c:C) -> Self {MonoidalString{string:vec![c],rules:PhantomData}}
}

impl<C,A:?Sized,M:?Sized> AsRef<[C]> for MonoidalString<C,A,M> { #[inline] fn as_ref(&self) -> &[C] {self.string.as_ref()} }
impl<C,A:?Sized,M:?Sized> Borrow<[C]> for MonoidalString<C,A,M> { #[inline] fn borrow(&self) -> &[C] {self.string.borrow()} }

impl<C,A:?Sized,M:?Sized,I> Index<I> for MonoidalString<C,A,M> where Vec<C>:Index<I> {
    type Output = <Vec<C> as Index<I>>::Output;
    #[inline] fn index(&self, i:I) -> &Self::Output {&self.string[i]}
}

impl<C,A:?Sized,M:?Sized> IntoIterator for MonoidalString<C,A,M> {
    type Item = <Vec<C> as IntoIterator>::Item;
    type IntoIter = <Vec<C> as IntoIterator>::IntoIter;
    #[inline] fn into_iter(self) -> Self::IntoIter { self.string.into_iter() }
}

impl<C,A:MonoidRule<C>+?Sized,M:?Sized> Sum<C> for MonoidalString<C,A,M> {
    fn sum<I:Iterator<Item=C>>(iter: I) -> Self {
        Self { string: A::apply_iter(Vec::with_capacity(0), iter), rules: PhantomData }
    }
}

impl<C,A:MonoidRule<C>+?Sized,M:?Sized> Sum for MonoidalString<C,A,M> {
    fn sum<I:Iterator<Item=Self>>(iter: I) -> Self { iter.fold(Self::zero(), |a,b| a+b) }
}

impl<C,A:?Sized,M:MonoidRule<C>+?Sized> Product<C> for MonoidalString<C,A,M> {
    fn product<I:Iterator<Item=C>>(iter: I) -> Self {
        Self { string: M::apply_iter(Vec::with_capacity(0), iter), rules: PhantomData }
    }
}

impl<C,A:?Sized,M:MonoidRule<C>+?Sized> Product for MonoidalString<C,A,M> {
    fn product<I:Iterator<Item=Self>>(iter: I) -> Self { iter.fold(Self::one(), |a,b| a*b) }
}

impl<C,A:?Sized,M:?Sized> MonoidalString<C,A,M> {
    #[inline] pub fn iter(&self) -> std::slice::Iter<C> { self.string.iter() }
}

pub trait MonoidRule<C> {
    fn apply(string: Vec<C>, letter: C) -> Vec<C>;
    fn apply_many(string1: Vec<C>, string2: Vec<C>) -> Vec<C> {Self::apply_iter(string1, string2.into_iter())}
    fn apply_iter<I:Iterator<Item=C>>(mut string: Vec<C>, letters: I) -> Vec<C> {
        string.reserve(letters.size_hint().0);
        letters.fold(string, |s,c| Self::apply(s,c))
    }

}

pub trait InvMonoidRule<C>: MonoidRule<C> { fn invert(letter: C) -> C; }

impl<C,A:AddAssociative+?Sized,M:?Sized> AddAssociative for MonoidalString<C,A,M> {}
impl<C,A:AddCommutative+?Sized,M:?Sized> AddCommutative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:MulAssociative+?Sized> MulAssociative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:MulCommutative+?Sized> MulCommutative for MonoidalString<C,A,M> {}
impl<C,A,M:?Sized> Distributive for MonoidalString<C,A,M> where M:Distributive<A> {}

impl<C,A:?Sized,M:?Sized> MonoidalString<C,A,M> {

    fn apply<R:MonoidRule<C>+?Sized>(&mut self, rhs:Self) {
        //swap out string with a dummy vec so we don't violate move rules
        let mut temp = Vec::with_capacity(0);
        ::std::mem::swap(&mut self.string, &mut temp);

        //apply the monoid rule
        self.string = R::apply_many(temp, rhs.string);
    }

    fn invert<R:InvMonoidRule<C>+?Sized>(self) -> Self {
        Self {
            string: R::apply_iter(Vec::with_capacity(0), self.string.into_iter().rev().map(|c| R::invert(c))),
            rules: PhantomData
        }
    }
}

impl<C,A:MonoidRule<C>+?Sized,M:?Sized> AddAssign for MonoidalString<C,A,M> {
    #[inline] fn add_assign(&mut self, rhs:Self) { self.apply::<A>(rhs) }
}
impl<C,A:?Sized,M:MonoidRule<C>+?Sized> MulAssign for MonoidalString<C,A,M> {
    #[inline] fn mul_assign(&mut self, rhs:Self) { self.apply::<M>(rhs) }
}
impl<C,A:InvMonoidRule<C>+?Sized,M:?Sized> SubAssign for MonoidalString<C,A,M> {
    #[inline] fn sub_assign(&mut self, rhs:Self) { *self+=-rhs }
}
impl<C,A:?Sized,M:InvMonoidRule<C>+?Sized> DivAssign for MonoidalString<C,A,M> {
    #[inline] fn div_assign(&mut self, rhs:Self) { *self*=rhs.inv() }
}

impl<C,A:MonoidRule<C>+?Sized,M:?Sized> Zero for MonoidalString<C,A,M> {
    #[inline] fn zero() -> Self { Default::default() }
    #[inline] fn is_zero(&self) -> bool { self.string.len()==0 }
}

impl<C,A:?Sized,M:MonoidRule<C>+?Sized> One for MonoidalString<C,A,M> {
    #[inline] fn one() -> Self { Default::default() }
    #[inline] fn is_one(&self) -> bool { self.string.len()==0 }
}

impl<C,A:InvMonoidRule<C>+?Sized,M:?Sized> Neg for MonoidalString<C,A,M> {
    type Output = Self; #[inline] fn neg(self) -> Self {self.invert::<A>()}
}
impl<C,A:?Sized,M:InvMonoidRule<C>+?Sized> Inv for MonoidalString<C,A,M> {
    type Output = Self; #[inline] fn inv(self) -> Self {self.invert::<M>()}
}

from_assign!(impl<C,A,M,X> Add<X>.add for MonoidalString<C,A,M> with += where A:?Sized, M:?Sized, Self:AddAssign<X>);
from_assign!(impl<C,A,M,X> Sub<X>.sub for MonoidalString<C,A,M> with -= where A:?Sized, M:?Sized, Self:SubAssign<X>);
from_assign!(impl<C,A,M,X> Mul<X>.mul for MonoidalString<C,A,M> with *= where A:?Sized, M:?Sized, Self:MulAssign<X>);
from_assign!(impl<C,A,M,X> Div<X>.div for MonoidalString<C,A,M> with /= where A:?Sized, M:?Sized, Self:DivAssign<X>);

#[marker] #[doc(hidden)] pub trait PowMarker<T> {}
impl<Z:IntegerSubset,C,A:?Sized,M:InvMonoidRule<C>+?Sized> PowMarker<Z> for MonoidalString<C,A,M> {}
impl<Z:Natural,C,A:?Sized,M:MonoidRule<C>+?Sized> PowMarker<Z> for MonoidalString<C,A,M> {}

impl<Z:IntegerSubset,C:Clone,A:?Sized,M:MonoidRule<C>+?Sized> Pow<Z> for MonoidalString<C,A,M>
where Self:PowMarker<Z> + MulAssociative
{
    type Output = Self;
    default fn pow(self, p:Z) -> Self { repeated_squaring(self, p.as_unsigned()) }
}

impl<Z:IntegerSubset,C:Clone,A:?Sized,M:InvMonoidRule<C>+?Sized> Pow<Z> for MonoidalString<C,A,M>
where Self:PowMarker<Z> + MulAssociative
{
    fn pow(self, p:Z) -> Self { repeated_squaring_inv(self, p) }
}
