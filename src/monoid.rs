use super::*;

use std::ops::Index;

#[derive(Derivative)]
#[derivative(Clone(clone_from="true"))]
#[derivative(Default(bound=""))]
#[derivative(PartialEq, Eq, Hash)]
#[derivative(Debug="transparent")]
pub struct MonoidalString<C,M:?Sized> {
    #[derivative(Default(value="Vec::with_capacity(0)"))]
    string: Vec<C>,

    #[derivative(PartialEq="ignore", Hash="ignore")]
    #[derivative(Debug="ignore")]
    rules: PhantomData<M>
}

///Iterates over immutable references of the letters of a [MonoidalString]
pub type Iter<'a,C> = std::slice::Iter<'a,C>;

///Iterates over the letters of a [MonoidalString]
pub type IntoIter<C> = <Vec<C> as IntoIterator>::IntoIter;

impl<C,M:?Sized> From<C> for MonoidalString<C,M> {
    #[inline] fn from(c:C) -> Self {MonoidalString{string:vec![c],rules:PhantomData}}
}

impl<C,M:?Sized> AsRef<[C]> for MonoidalString<C,M> { #[inline] fn as_ref(&self) -> &[C] {self.string.as_ref()} }
impl<C,M:?Sized> Borrow<[C]> for MonoidalString<C,M> { #[inline] fn borrow(&self) -> &[C] {self.string.borrow()} }

impl<C,M:?Sized,I> Index<I> for MonoidalString<C,M> where Vec<C>:Index<I> {
    type Output = <Vec<C> as Index<I>>::Output;
    #[inline] fn index(&self, i:I) -> &Self::Output {&self.string[i]}
}

impl<C,M:?Sized> IntoIterator for MonoidalString<C,M> {
    type Item = C;
    type IntoIter = IntoIter<C>;
    #[inline] fn into_iter(self) -> IntoIter<C> { self.string.into_iter() }
}

impl<C,M:MonoidRule<C>+?Sized> Product<C> for MonoidalString<C,M> {
    fn product<I:Iterator<Item=C>>(iter: I) -> Self {
        Self { string: M::apply_iter(Vec::with_capacity(0), iter), rules: PhantomData }
    }
}

impl<C,M:MonoidRule<C>+?Sized> Product for MonoidalString<C,M> {
    fn product<I:Iterator<Item=Self>>(iter: I) -> Self { iter.fold(Self::one(), |a,b| a*b) }
}

impl<C,M:?Sized> MonoidalString<C,M> {
    ///Produces an iterator over references to the letters in this element
    #[inline] pub fn iter(&self) -> Iter<C> { self.string.iter() }
}

///
///Dictates a rule for how to multiply or add letters to a [MonoidalString]'s word
///
///The simplest possible version of this simply applies multiplication as simple concatenation,
///but this trait is robust enough to support more complex operations such as for [FreeGroup]
///
pub trait MonoidRule<C> {
    ///Applies the operation rule to the product of a word and a single letter
    fn apply(word: Vec<C>, letter: C) -> Vec<C>;

    ///
    ///Applies the operation rule to the product of two words
    ///
    ///By default, this computes the result by individually applying the rule to each letter of the
    ///second word to the first using [MonoidRule::apply]
    ///
    fn apply_many(word1: Vec<C>, word2: Vec<C>) -> Vec<C> {Self::apply_iter(word1, word2.into_iter())}

    ///
    ///Applies the operation rule to the product of a word and a sequence of letters
    ///
    ///By default, this computes the result by individually applying the rule to each letter in
    ///sequence to the first using [MonoidRule::apply]
    ///
    fn apply_iter<I:Iterator<Item=C>>(mut word: Vec<C>, letters: I) -> Vec<C> {
        word.reserve(letters.size_hint().0);
        letters.fold(word, |s,c| Self::apply(s,c))
    }

}

///A [MonoidRule] where each letter has a notion of an inverse
pub trait InvMonoidRule<C>: MonoidRule<C> {
    ///Inverts a letter `x` such that `x * x.invert() == 1`
    fn invert(letter: C) -> C;
}

///A [MonoidRule] that is evaluation order independent
#[marker] pub trait AssociativeMonoidRule<C>: MonoidRule<C> {}

///A [MonoidRule] that is order independent
#[marker] pub trait CommutativeMonoidRule<C>: MonoidRule<C> {}

impl<C,M:AssociativeMonoidRule<C>+?Sized> MulAssociative for MonoidalString<C,M> {}
impl<C,M:CommutativeMonoidRule<C>+?Sized> MulCommutative for MonoidalString<C,M> {}

impl<C,M:?Sized> MonoidalString<C,M> {

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

    ///An operation agnostic method for computing inverses
    fn invert<R:InvMonoidRule<C>+?Sized>(self) -> Self {
        Self {
            string: R::apply_iter(Vec::with_capacity(0), self.string.into_iter().rev().map(|c| R::invert(c))),
            rules: PhantomData
        }
    }
}

impl<C,M:MonoidRule<C>+?Sized> MulAssign<C> for MonoidalString<C,M> {
    #[inline] fn mul_assign(&mut self, rhs:C) { self.apply_one::<M>(rhs) }
}
impl<C,M:InvMonoidRule<C>+?Sized> DivAssign<C> for MonoidalString<C,M> {
    #[inline] fn div_assign(&mut self, rhs:C) { *self*=M::invert(rhs) }
}

impl<C,M:MonoidRule<C>+?Sized> MulAssign for MonoidalString<C,M> {
    #[inline] fn mul_assign(&mut self, rhs:Self) { self.apply::<M>(rhs) }
}
impl<C,M:InvMonoidRule<C>+?Sized> DivAssign for MonoidalString<C,M> {
    #[inline] fn div_assign(&mut self, rhs:Self) { *self*=rhs.inv() }
}

impl<C,M:MonoidRule<C>+?Sized> One for MonoidalString<C,M> {
    #[inline] fn one() -> Self { Default::default() }
    #[inline] fn is_one(&self) -> bool { self.string.len()==0 }
}

impl<C,M:InvMonoidRule<C>+?Sized> Inv for MonoidalString<C,M> {
    type Output = Self; #[inline] fn inv(self) -> Self {self.invert::<M>()}
}

impl<C:Clone,M:InvMonoidRule<C>+AssociativeMonoidRule<C>+?Sized> MonoidalString<C,M> {
    ///Computes the multiplicative commutator `[a,b] = a⁻¹b⁻¹ab`
    pub fn commutator(self, rhs:Self) -> Self { self.clone().inv()*rhs.clone()*self*rhs }
}

from_assign!(impl<C,M,X> Mul<X>.mul for MonoidalString<C,M> with *= where M:?Sized, Self:MulAssign<X>);
from_assign!(impl<C,M,X> Div<X>.div for MonoidalString<C,M> with /= where M:?Sized, Self:DivAssign<X>);

#[marker] #[doc(hidden)] pub trait PowMarker<T> {}
impl<Z:IntegerSubset,C,M:InvMonoidRule<C>+?Sized> PowMarker<Z> for MonoidalString<C,M> {}
impl<Z:Natural,C,M:MonoidRule<C>+?Sized> PowMarker<Z> for MonoidalString<C,M> {}

impl<Z:IntegerSubset,C:Clone,M:MonoidRule<C>+?Sized> Pow<Z> for MonoidalString<C,M>
where Self:PowMarker<Z> + MulAssociative
{
    type Output = Self;
    default fn pow(self, p:Z) -> Self { repeated_squaring(self, p.as_unsigned()) }
}

impl<Z:IntegerSubset,C:Clone,M:InvMonoidRule<C>+?Sized> Pow<Z> for MonoidalString<C,M>
where Self:PowMarker<Z> + MulAssociative
{
    fn pow(self, p:Z) -> Self { repeated_squaring_inv(self, p) }
}
