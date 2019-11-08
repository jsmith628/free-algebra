use super::*;

///
///A [FreeMonoid], but where each letter can be inverted
///
///In essence, this entails constructing a [FreeMonoid] over [FreeInv<C>](FreeInv) with the same
///multiplication _except_ that elements cancel with their inverses
///
///# Examples
///```
///use maths_traits::algebra::{One, Inv};
///use free_algebra::FreeGroup;
///
///use free_algebra::FreeInv::*;
///
///let x = Id('a') * Id('b').inv() * Id('c');
///let y = (&x).inv();
///
///assert_eq!(x, [Id('a'), Inv('b'), Id('c')]);
///assert_eq!(y, [Inv('c'), Id('b'), Inv('a')]);
///assert!((&x / &x).is_one());
///assert!((&y * &x).is_one());
///assert!((&x * &y).is_one());
///
///let mul = &x * Id('d') * (&y);
///assert_eq!(mul, [Id('a'), Inv('b'), Id('c'), Id('d'), Inv('c'), Id('b'), Inv('a')]);
///
///```
///
pub type FreeGroup<C> = MonoidalString<FreeInv<C>,InvRule>;

///
///Wraps a type `T` and symbolically inverts elements.
///
///Used for constructing [FreeGroup]
///
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FreeInv<T:Eq> {
    ///Wraps an instance of type `T`
    Id(T),
    ///The symbolic inverse of an object of type `T`
    Inv(T)
}

impl<T:Eq> From<T> for FreeInv<T> {
    fn from(t:T) -> Self { FreeInv::Id(t) }
}

///
///Provides a reference to this type's inner `T`
///
///Note that this does not convey any information regarding the state of inversion
///
impl<T:Eq> AsRef<T> for FreeInv<T> {
    fn as_ref(&self) -> &T {
        match self {
            FreeInv::Id(ref x) => x,
            FreeInv::Inv(ref x) => x
        }
    }
}

///
///Provides a mutable reference to this type's inner `T`
///
///Note that this does not convey any information regarding the state of inversion
///
impl<T:Eq> AsMut<T> for FreeInv<T> {
    fn as_mut(&mut self) -> &mut T {
        match self {
            FreeInv::Id(ref mut x) => x,
            FreeInv::Inv(ref mut x) => x
        }
    }
}

impl<T:Eq> PartialEq<T> for FreeInv<T> {
    fn eq(&self, rhs:&T) -> bool {
        match self {
            FreeInv::Id(x) => x==rhs,
            FreeInv::Inv(_) => false
        }
    }
}

impl<T:Eq+Display> Display for FreeInv<T> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        match self {
            Self::Id(x) => write!(f, "{}", x),
            Self::Inv(x) => write!(f, "{}⁻¹", x),
        }
    }
}

impl<T:Eq> FreeInv<T> {

    ///
    ///Returns true if `self` is [inverted](FreeInv::Inv)
    ///
    ///```
    ///use free_algebra::FreeInv::*;
    ///
    ///assert!(Inv('a').is_inv());
    ///assert!(!Id('a').is_inv());
    ///```
    ///
    pub fn is_inv(&self) -> bool {
        match self { Self::Inv(_) => true, _ => false }
    }

    ///
    ///Returns true if `self` is [non-inverted](FreeInv::Inv)
    ///
    ///```
    ///use free_algebra::FreeInv::*;
    ///
    ///assert!(Id('a').is_id());
    ///assert!(!Inv('a').is_id());
    ///```
    ///
    pub fn is_id(&self) -> bool {
        match self { Self::Id(_) => true, _ => false }
    }

    ///Determines if two objects are inverses
    fn are_inverses(&self, rhs:&Self) -> bool {
        self.as_ref()==rhs.as_ref() && self.is_inv()^rhs.is_inv()
    }
}

///Multiplication of [FreeInv] elements using concatenation with inverse cancellation
pub struct InvRule;

impl<T:Eq> AssociativeMonoidRule<FreeInv<T>> for InvRule {}
impl<T:Eq> MonoidRule<FreeInv<T>> for InvRule {
    fn apply(mut string: Vec<FreeInv<T>>, letter: FreeInv<T>) -> Vec<FreeInv<T>> {
        if string.last().map_or(false, |last| letter.are_inverses(last)) {
            string.pop();
        } else {
            string.push(letter);
        }
        string
    }
}

impl<T:Eq> InvMonoidRule<FreeInv<T>> for InvRule {
    fn invert(letter: FreeInv<T>) -> FreeInv<T> { letter.inv() }
}

impl<T:Eq> Inv for FreeInv<T> {
    type Output = Self;
    fn inv(self) -> Self {
        match self {
            Self::Id(x) => Self::Inv(x),
            Self::Inv(x) => Self::Id(x)
        }
    }
}

impl<T:Eq> Mul for FreeInv<T> {
    type Output = FreeGroup<T>;
    fn mul(self, rhs:Self) -> FreeGroup<T> { FreeGroup::from(self) * rhs }
}

impl<T:Eq> Div for FreeInv<T> {
    type Output = FreeGroup<T>;
    fn div(self, rhs:Self) -> FreeGroup<T> { self * rhs.inv() }
}

impl<T:Eq> Mul<FreeGroup<T>> for FreeInv<T> {
    type Output = FreeGroup<T>;
    fn mul(self, rhs:FreeGroup<T>) -> FreeGroup<T> { FreeGroup::from(self) * rhs }
}

impl<T:Eq> Div<FreeGroup<T>> for FreeInv<T> {
    type Output = FreeGroup<T>;
    fn div(self, rhs:FreeGroup<T>) -> FreeGroup<T> { FreeGroup::from(self) / rhs }
}
