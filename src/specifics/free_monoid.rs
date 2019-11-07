use super::*;

///
///A [monoid](MulMonoid) constructed from free multiplication of elements of a set
///
///Concretely, given a set `C`, we construct the free-monoid of `C` as the set of all finite lists
///of members of `C` where multiplication is given by concatenation. In other words, it's basically
///[`Vec<C>`](Vec) but with `a*b == {a.append(&mut b); a}`.
///
///```
///use maths_traits::algebra::One;
///use free_algebra::FreeMonoid;
///
///let s1 = FreeMonoid::one() * 'a' * 'b' * 'c';
///let s2 = s1.clone().reverse();
///
///assert_eq!(s1, ['a','b','c']);
///assert_eq!(s2, ['c','b','a']);
///
///let mul = s1 * s2;
///
///assert_eq!(mul, ['a','b','c','c','b','a']);
///
///```
///
pub type FreeMonoid<C> = MonoidalString<C,()>;

impl<C> AssociativeMonoidRule<C> for () {}
impl<C> MonoidRule<C> for () {
    fn apply(mut string: Vec<C>, letter: C) -> Vec<C> {string.push(letter); string}
    fn apply_many(mut string1: Vec<C>, mut string2: Vec<C>) -> Vec<C> {
        string1.append(&mut string2); string1
    }
    fn apply_iter<I:Iterator<Item=C>>(mut string: Vec<C>, letters: I) -> Vec<C> {
        string.extend(letters); string
    }
}
