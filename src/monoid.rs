use super::*;

use std::ops::Index;

#[derive(Derivative)]
#[derivative(Clone(clone_from="true"))]
#[derivative(Default(bound=""))]
#[derivative(Hash)]
#[derivative(Debug="transparent")]
pub struct MonoidalString<C,M:?Sized> {
    #[derivative(Default(value="Vec::with_capacity(0)"))]
    string: Vec<C>,

    #[derivative(PartialEq="ignore", Hash="ignore")]
    #[derivative(Debug="ignore")]
    rule: PhantomData<M>
}

impl<C:Eq,M:?Sized> Eq for MonoidalString<C,M> {}
impl<C:PartialEq,M:?Sized,V:Borrow<[C]>> PartialEq<V> for MonoidalString<C,M> {
    fn eq(&self, rhs:&V) -> bool {Borrow::<[C]>::borrow(self) == Borrow::<[C]>::borrow(rhs)}
    fn ne(&self, rhs:&V) -> bool {Borrow::<[C]>::borrow(self) != Borrow::<[C]>::borrow(rhs)}
}

///
///Formats the [MonoidalString] as a sequence of factors separated by `*`'s
///
///# Examples
///
///```
///use maths_traits::algebra::One;
///use free_algebra::FreeMonoid;
///
///let x = FreeMonoid::one() * 'a' * 'b' * 'c';
///assert_eq!(format!("{}", x), "a*b*c");
///
///```
///
///```
///use maths_traits::algebra::*;
///use free_algebra::FreeInv::*;
///
///let y = Id('a') * Inv('b') * Inv('a') * Id('c');
///assert_eq!(format!("{}", y), "a*b⁻¹*a⁻¹*c");
///```
///
///Note that if the "alternate" flag `#` is used, then the `*`'s will be dropped.
///
///```
///use maths_traits::algebra::One;
///use free_algebra::FreeMonoid;
///
///let x = FreeMonoid::one() * 'a' * 'b' * 'c';
///assert_eq!(format!("{:#}", x), "abc");
///
///```
///
///```
///use maths_traits::algebra::*;
///use free_algebra::FreeInv::*;
///
///let y = Id('a') * Inv('b') * Inv('a') * Id('c');
///assert_eq!(format!("{:#}", y), "ab⁻¹a⁻¹c");
///```
///
impl<C:Display,M:?Sized> Display for MonoidalString<C,M> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        if self.len()==0 {
            write!(f, "{}", 1)
        } else {
            //print letters as a product
            for i in 0..self.len() {
                if i!=0 && !f.alternate() { write!(f, "*")? }
                write!(f, "{}", self[i])?
            }

            //success
            Ok(())
        }
    }
}

///Iterates over immutable references of the letters of a [MonoidalString]
pub type Iter<'a,C> = std::slice::Iter<'a,C>;

///Iterates over the letters of a [MonoidalString]
pub type IntoIter<C> = <Vec<C> as IntoIterator>::IntoIter;

///
///Iterates over mutable references to the letters of a [MonoidalString]
///
///Note that this causes a reallocation of the internal [Vec] since it's possible that an
///element mutation could create an illegal state if not reconstructed from the sums of the mutated
///terms.
///
pub struct IterMut<'a, C, M:MonoidRule<C>+?Sized> {
    dest_ref: &'a mut MonoidalString<C,M>,
    next: Option<C>,
    iter: IntoIter<C>
}

impl<'a,C,M:MonoidRule<C>+?Sized> FusedIterator for IterMut<'a,C,M> {}
impl<'a,C,M:MonoidRule<C>+?Sized> ExactSizeIterator for IterMut<'a,C,M> {}
impl<'a,C,M:MonoidRule<C>+?Sized> Iterator for IterMut<'a,C,M> {
    type Item = &'a mut C;
    fn next(&mut self) -> Option<&'a mut C> {
        self.next.take().map(|c| *self.dest_ref *= c);
        self.next = self.iter.next();

        //we know that the given reference is lifetime 'a because in order for next to be dropped,
        //either self must be borrowed mutably again or dropped, which cannot happen while the reference lives
        self.next.as_mut().map(|c| unsafe {&mut *(c as *mut C)} )
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a,C,M:MonoidRule<C>+?Sized> Drop for IterMut<'a,C,M> {
    fn drop(&mut self) {
        loop { if let None = self.next() {break;} }
    }
}

impl<C,M:?Sized> From<C> for MonoidalString<C,M> {
    #[inline] fn from(c:C) -> Self {MonoidalString{string:vec![c],rule:PhantomData}}
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

impl<C,M:MonoidRule<C>+?Sized> Extend<C> for MonoidalString<C,M> {
    fn extend<I:IntoIterator<Item=C>>(&mut self, iter:I) {
        self.apply_fn(|string| M::apply_iter(string, iter.into_iter()))
    }
}

impl<C,M:?Sized,T> FromIterator<T> for MonoidalString<C,M> where Self:Product<T> {
    fn from_iter<I:IntoIterator<Item=T>>(iter:I) -> Self { iter.into_iter().product() }
}

impl<C,M:MonoidRule<C>+?Sized> Product<C> for MonoidalString<C,M> {
    fn product<I:Iterator<Item=C>>(iter: I) -> Self {
        let mut dest:Self = One::one();
        dest.extend(iter);
        dest
    }
}

impl<C,M:MonoidRule<C>+?Sized> Product for MonoidalString<C,M> {
    fn product<I:Iterator<Item=Self>>(iter: I) -> Self { iter.flatten().product() }
}

impl<C,M:?Sized> MonoidalString<C,M> {

    ///
    ///Returns the number of letters in this monoidal-string
    ///
    ///## Examples
    ///```
    ///use maths_traits::algebra::One;
    ///use free_algebra::FreeMonoid;
    ///
    ///let x = FreeMonoid::one();
    ///let y = x.clone() * 'a' * 'a';
    ///
    ///assert_eq!(x.len(), 0);
    ///assert_eq!(y.len(), 2);
    ///
    ///```
    ///
    #[inline] pub fn len(&self) -> usize { self.string.len() }

    ///
    ///Produces an iterator over references to the letters in this element
    ///
    ///## Examples
    ///```
    ///use maths_traits::algebra::One;
    ///use free_algebra::FreeMonoid;
    ///
    ///let x = FreeMonoid::one() * 'a' * 'b' * 'c';
    ///let mut iter = x.iter();
    ///
    ///assert_eq!(iter.next(), Some(&'a'));
    ///assert_eq!(iter.next(), Some(&'b'));
    ///assert_eq!(iter.next(), Some(&'c'));
    ///assert_eq!(iter.next(), None);
    ///
    ///```
    ///
    #[inline] pub fn iter(&self) -> Iter<C> { self.string.iter() }

    ///
    ///Produces an iterator over mutable references to the letters in this element
    ///
    ///Note that the potential for modification does mean that the element needs to be remultiplied
    ///as letters are changed, so a potential reallocation of space may occur.
    ///
    ///## Examples
    ///```
    ///use free_algebra::{FreePow, FreePowMonoid};
    ///
    ///let x = FreePow('a',1) * FreePow('b',1) * FreePow('c',1);
    ///let mut y = x.clone();
    ///
    ///for FreePow(c,p) in y.iter_mut() {
    ///    *c = 'a';
    ///}
    ///
    ///assert_eq!(x, [FreePow('a',1), FreePow('b',1), FreePow('c',1)]);
    ///assert_eq!(y, [FreePow('a',3)]);
    ///
    ///```
    ///
    #[inline] pub fn iter_mut(&mut self) -> IterMut<C,M> where M:MonoidRule<C> {
        let mut temp = Self { string: Vec::with_capacity(self.len()), rule:PhantomData };
        ::std::mem::swap(self, &mut temp);
        IterMut { dest_ref: self, next: None, iter: temp.into_iter() }
    }

    ///
    ///Reverses the letters in this element and remultiplies
    ///
    ///## Examples
    ///```
    ///use maths_traits::algebra::One;
    ///use free_algebra::FreeMonoid;
    ///
    ///let x = FreeMonoid::one() * 'a' * 'b' * 'c';
    ///let y = x.clone().reverse();
    ///
    ///assert_eq!(x, ['a', 'b', 'c']);
    ///assert_eq!(y, ['c', 'b', 'a']);
    ///
    ///```
    pub fn reverse(self) -> Self where Self:Product<C> {
        self.into_iter().rev().product()
    }

    ///
    ///Computes the multiplicative commutator `[a,b] = a⁻¹b⁻¹ab`
    ///
    ///## Examples
    ///```
    ///use free_algebra::FreeGroup;
    ///use free_algebra::FreeInv::*;
    ///
    ///let x:FreeGroup<_> = Id('a').into();
    ///let y:FreeGroup<_> = Id('b').into();
    ///
    ///assert_eq!(x, [Id('a')]);
    ///assert_eq!(y, [Id('b')]);
    ///assert_eq!(x.commutator(y), [Inv('a'), Inv('b'), Id('a'), Id('b')]);
    ///
    ///```
    ///
    ///Note that a significant property of this product is that when the arguments commute, the
    ///output is always `1`.
    ///
    ///```
    ///```
    ///
    pub fn commutator(self, rhs:Self) -> Self where Self:MulMonoid+Inv<Output=Self> {
        self.clone().inv()*rhs.clone().inv()*self*rhs
    }
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

    ///Applies a move-semantic function by reference
    fn apply_fn<F:FnOnce(Vec<C>)->Vec<C>>(&mut self, f:F) {
        //swap out string with a dummy vec so we don't violate move rule
        let mut temp = Vec::with_capacity(0);
        ::std::mem::swap(&mut self.string, &mut temp);

        //apply the monoid rule
        self.string = f(temp);
    }

    ///An operation agnostic method for computing inverses
    fn invert<R:InvMonoidRule<C>+?Sized>(self) -> Self {
        Self {
            string: R::apply_iter(Vec::with_capacity(0), self.string.into_iter().rev().map(|c| R::invert(c))),
            rule: PhantomData
        }
    }
}

impl<C,M:MonoidRule<C>+?Sized> MulAssign<C> for MonoidalString<C,M> {
    fn mul_assign(&mut self, rhs:C) {
        self.apply_fn(|string| M::apply(string,rhs));
    }
}
impl<C,M:InvMonoidRule<C>+?Sized> DivAssign<C> for MonoidalString<C,M> {
    #[inline] fn div_assign(&mut self, rhs:C) { *self*=M::invert(rhs) }
}

impl<C,M:MonoidRule<C>+?Sized> MulAssign for MonoidalString<C,M> {
    fn mul_assign(&mut self, rhs:Self) {
        self.apply_fn(|string| M::apply_many(string,rhs.string));
    }
}
impl<C,M:InvMonoidRule<C>+?Sized> DivAssign for MonoidalString<C,M> {
    #[inline] fn div_assign(&mut self, rhs:Self) { *self*=rhs.inv() }
}

impl_arith!(impl<C,M> MulAssign<&C>.mul_assign for MonoidalString<C,M> where M:?Sized);
impl_arith!(impl<C,M> DivAssign<&C>.div_assign for MonoidalString<C,M> where M:?Sized);

impl_arith!(impl<C,M> MulAssign<&Self>.mul_assign for MonoidalString<C,M> where M:?Sized);
impl_arith!(impl<C,M> DivAssign<&Self>.div_assign for MonoidalString<C,M> where M:?Sized);

impl_arith!(impl<C,M> Mul.mul with MulAssign.mul_assign for MonoidalString<C,M> where M:?Sized);
impl_arith!(impl<C,M> Div.div with DivAssign.div_assign for MonoidalString<C,M> where M:?Sized);

impl<C,M:MonoidRule<C>+?Sized> One for MonoidalString<C,M> {
    #[inline] fn one() -> Self { Default::default() }
    #[inline] fn is_one(&self) -> bool { self.string.len()==0 }
}

impl<C,M:InvMonoidRule<C>+?Sized> Inv for MonoidalString<C,M> {
    type Output = Self;
    #[inline] fn inv(self) -> Self {self.invert::<M>()}
}

impl<'a,C,M:InvMonoidRule<C>+?Sized> Inv for &'a MonoidalString<C,M> where MonoidalString<C,M>:Clone {
    type Output = MonoidalString<C,M>;
    #[inline] fn inv(self) -> Self::Output {(*self).clone().inv()}
}

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
