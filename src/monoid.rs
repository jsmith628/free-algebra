use super::*;

use std::ops::Index;

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

pub type Iter<'a,C> = std::slice::Iter<'a,C>;
pub type IntoIter<C> = <Vec<C> as IntoIterator>::IntoIter;

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
    type Item = C;
    type IntoIter = IntoIter<C>;
    #[inline] fn into_iter(self) -> IntoIter<C> { self.string.into_iter() }
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
    #[inline] pub fn iter(&self) -> Iter<C> { self.string.iter() }
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

#[marker] pub trait AssociativeRule<C>: MonoidRule<C> {}
#[marker] pub trait CommutativeRule<C>: MonoidRule<C> {}
#[marker] pub trait DistributiveRule<C,A:MonoidRule<C>>: MonoidRule<C> {}

impl<C,A:AssociativeRule<C>+?Sized,M:?Sized> AddAssociative for MonoidalString<C,A,M> {}
impl<C,A:CommutativeRule<C>+?Sized,M:?Sized> AddCommutative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:AssociativeRule<C>+?Sized> MulAssociative for MonoidalString<C,A,M> {}
impl<C,A:?Sized,M:CommutativeRule<C>+?Sized> MulCommutative for MonoidalString<C,A,M> {}
impl<C,A:MonoidRule<C>,M:?Sized> Distributive for MonoidalString<C,A,M> where M:DistributiveRule<C,A> {}

impl<C,A:?Sized,M:?Sized> MonoidalString<C,A,M> {

    fn apply_one<R:MonoidRule<C>+?Sized>(&mut self, rhs:C) {
        //swap out string with a dummy vec so we don't violate move rules
        let mut temp = Vec::with_capacity(0);
        ::std::mem::swap(&mut self.string, &mut temp);

        //apply the monoid rule
        self.string = R::apply(temp,rhs);
    }

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

impl<C,A:MonoidRule<C>+?Sized,M:?Sized> AddAssign<C> for MonoidalString<C,A,M> {
    #[inline] fn add_assign(&mut self, rhs:C) { self.apply_one::<A>(rhs) }
}
impl<C,A:?Sized,M:MonoidRule<C>+?Sized> MulAssign<C> for MonoidalString<C,A,M> {
    #[inline] fn mul_assign(&mut self, rhs:C) { self.apply_one::<M>(rhs) }
}
impl<C,A:InvMonoidRule<C>+?Sized,M:?Sized> SubAssign<C> for MonoidalString<C,A,M> {
    #[inline] fn sub_assign(&mut self, rhs:C) { *self+=A::invert(rhs) }
}
impl<C,A:?Sized,M:InvMonoidRule<C>+?Sized> DivAssign<C> for MonoidalString<C,A,M> {
    #[inline] fn div_assign(&mut self, rhs:C) { *self*=M::invert(rhs) }
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

impl<C:Clone,A:?Sized,M:InvMonoidRule<C>+AssociativeRule<C>+?Sized> MonoidalString<C,A,M> {
    pub fn commutator(self, rhs:Self) -> Self { self.clone().inv()*rhs.clone()*self*rhs }
}

impl<C:Clone,A:InvMonoidRule<C>+AssociativeRule<C>+?Sized,M:?Sized> MonoidalString<C,A,M> {
    pub fn add_commutator(self, rhs:Self) -> Self { -self.clone() - rhs.clone() + self + rhs }
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


impl<C> AssociativeRule<C> for () {}
impl<C> MonoidRule<C> for () {
    fn apply(mut string: Vec<C>, letter: C) -> Vec<C> {string.push(letter); string}
    fn apply_many(mut string1: Vec<C>, mut string2: Vec<C>) -> Vec<C> {
        string1.append(&mut string2); string1
    }
    fn apply_iter<I:Iterator<Item=C>>(mut string: Vec<C>, letters: I) -> Vec<C> {
        string.extend(letters); string
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct FreePow<C:Eq,Z:IntegerSubset>(pub C,pub Z);

pub struct PowRule;

impl<C:Eq,Z:IntegerSubset> AssociativeRule<FreePow<C,Z>> for PowRule {}
impl<C:Eq,Z:IntegerSubset> MonoidRule<FreePow<C,Z>> for PowRule {
    fn apply(mut string: Vec<FreePow<C,Z>>, letter: FreePow<C,Z>) -> Vec<FreePow<C,Z>> {
        if string.last().map_or(false, |l| l.0==letter.0) {
            let last = string.pop().unwrap();
            let last = FreePow(letter.0, last.1 + letter.1);
            if !last.1.is_zero() { string.push(last); }
        } else {
            string.push(letter);
        }
        string
    }
}

impl<C:Eq,Z:Integer> InvMonoidRule<FreePow<C,Z>> for PowRule {
    fn invert(FreePow(base, pow): FreePow<C,Z>) -> FreePow<C,Z> { FreePow(base, -pow) }
}

impl<C:Eq,Z:IntegerSubset> From<C> for FreePow<C,Z> { fn from(c:C) -> Self { (c,Z::one()).into() } }
impl<C:Eq,Z:IntegerSubset> From<(C,Z)> for FreePow<C,Z> { fn from((c,z):(C,Z)) -> Self { FreePow(c,z) } }

impl<C:Eq,Z:Integer> Inv for FreePow<C,Z> {
    type Output = Self;
    fn inv(self) -> Self { PowRule::invert(self) }
}

impl<C:Eq,Z:IntegerSubset> Mul for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn mul(self, rhs:Self) -> FreeGroup<C,Z> { FreeGroup::from(self) * rhs }
}

impl<C:Eq,Z:IntegerSubset> Mul<C> for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn mul(self, rhs:C) -> FreeGroup<C,Z> { self * Self::from(rhs) }
}

impl<C:Eq,Z:IntegerSubset> Mul<FreeGroup<C,Z>> for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn mul(self, rhs:FreeGroup<C,Z>) -> FreeGroup<C,Z> { FreeGroup::from(self) * rhs }
}

impl<C:Eq,Z:Integer> Div for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn div(self, rhs:Self) -> FreeGroup<C,Z> { self * rhs.inv() }
}

impl<C:Eq,Z:Integer> Div<C> for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn div(self, rhs:C) -> FreeGroup<C,Z> { self / Self::from(rhs) }
}

impl<C:Eq,Z:Integer> Div<FreeGroup<C,Z>> for FreePow<C,Z> {
    type Output = FreeGroup<C,Z>;
    fn div(self, rhs:FreeGroup<C,Z>) -> FreeGroup<C,Z> { FreeGroup::from(self) / rhs }
}

pub type FreeMonoid<C> = MonoidalString<C,(),()>;
pub type FreeGroup<C,Z> = MonoidalString<FreePow<C,Z>,!,PowRule>;
