
use maths_traits::algebra::*;

use std::marker::PhantomData;
use std::hash::{Hash, Hasher};
use std::ops::Index;
use std::borrow::Borrow;

pub struct MonoidalString<C,A:?Sized,M:?Sized> {
    string: Vec<C>,
    rules: PhantomData<(Box<A>,Box<M>)>
}

impl<C:Clone,A:?Sized,M:?Sized> Clone for MonoidalString<C,A,M> {
    #[inline] fn clone(&self) -> Self {MonoidalString{string:self.string.clone(), rules:PhantomData}}
}

impl<C:Eq,A:?Sized,M:?Sized> Eq for MonoidalString<C,A,M> {}
impl<C:PartialEq,A:?Sized,M:?Sized> PartialEq for MonoidalString<C,A,M> {
    #[inline] fn eq(&self, rhs:&Self) -> bool {self.string.eq(&rhs.string)}
    #[inline] fn ne(&self, rhs:&Self) -> bool {self.string.ne(&rhs.string)}
}

impl<C:Hash,A:?Sized,M:?Sized> Hash for MonoidalString<C,A,M> {
    #[inline] fn hash<H:Hasher>(&self, state: &mut H) {self.string.hash(state)}
}

impl<C,A:?Sized,M:?Sized> Default for MonoidalString<C,A,M> {
    #[inline] fn default() -> Self {MonoidalString{string:Vec::new(),rules:PhantomData}}
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

pub trait MonoidRule<C> { fn apply(string: Vec<C>, letter: C) -> Vec<C>; }

impl<C,A:AddAssociative+?Sized,M:?Sized> AddAssociative for MonoidalString<C,A,M> {}
impl<C,A:AddCommutative+?Sized,M:?Sized> AddCommutative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:MulAssociative+?Sized> MulAssociative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:MulCommutative+?Sized> MulCommutative for MonoidalString<C,A,M> {}
impl<C,A,M> Distributive for MonoidalString<C,A,M> where (A,M):Distributive {}

impl<C,A:?Sized,M:?Sized> MonoidalString<C,A,M> {
    fn apply<R:MonoidRule<C>+?Sized>(&mut self, rhs:Self) {
        self.string.reserve(rhs.string.len());
        let mut temp = Vec::new();
        ::std::mem::swap(&mut self.string, &mut temp);
        self.string = rhs.string.into_iter().fold(temp, |l,c| R::apply(l, c))
    }
    fn invert<F:Fn(C)->C>(self, f:F) -> Self {
        MonoidalString{
            string: self.string.into_iter().rev().map(|c| f(c)).collect(),
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
impl<C:Neg<Output=C>,A:MonoidRule<C>+?Sized,M:?Sized> SubAssign for MonoidalString<C,A,M> {
    #[inline] fn sub_assign(&mut self, rhs:Self) { *self+=-rhs }
}
impl<C:Inv<Output=C>,A:?Sized,M:MonoidRule<C>+?Sized> DivAssign for MonoidalString<C,A,M> {
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

impl<C:Neg<Output=C>,A:?Sized,M:?Sized> Neg for MonoidalString<C,A,M> {
    type Output = Self; #[inline] fn neg(self) -> Self {self.invert(|c| -c)}
}
impl<C:Inv<Output=C>,A:?Sized,M:?Sized> Inv for MonoidalString<C,A,M> {
    type Output = Self; #[inline] fn inv(self) -> Self {self.invert(|c| c.inv())}
}


from_assign!(impl<C,A,M,X> Add<X>.add for MonoidalString<C,A,M> with += where A:?Sized, M:?Sized, Self:AddAssign<X>);
from_assign!(impl<C,A,M,X> Sub<X>.sub for MonoidalString<C,A,M> with -= where A:?Sized, M:?Sized, Self:SubAssign<X>);
from_assign!(impl<C,A,M,X> Mul<X>.mul for MonoidalString<C,A,M> with *= where A:?Sized, M:?Sized, Self:MulAssign<X>);
from_assign!(impl<C,A,M,X> Div<X>.div for MonoidalString<C,A,M> with /= where A:?Sized, M:?Sized, Self:DivAssign<X>);
