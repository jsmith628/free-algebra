use super::*;

///
///A [FreeMonoid], but where each letter can be inverted
///
///In essence, this entails constructing a [FreeMonoid] over [FreeInv<C>](FreeInv) with the same
///multiplication _except_ that elements cancel with their inverses
///
///```
///use maths_traits::algebra::{One, Inv};
///use free_algebra::FreeGroup;
///
///use free_algebra::FreeInv::*;
///
///let g1 = Id('a') * Id('b').inv() * Id('c');
///let g2 = (&g1).inv();
///
///assert_eq!(g1, [Id('a'), Inv('b'), Id('c')]);
///assert_eq!(g2, [Inv('c'), Id('b'), Inv('a')]);
///assert!((&g1 * &g2).is_one());
///assert!((&g2 * &g1).is_one());
///
///let mul = g1 * Id('d') * g2;
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

    pub fn is_inv(&self) -> bool {
        match self { Self::Inv(_) => true, _ => false }
    }

    pub fn is_id(&self) -> bool {
        match self { Self::Id(_) => true, _ => false }
    }

    pub fn are_inverses(&self, rhs:&Self) -> bool {
        use FreeInv::*;
        match self {
            Id(x) => match rhs {
                Id(_) => false,
                Inv(y) => x==y
            },
            Inv(x) => match rhs {
                Id(y) => x==y,
                Inv(_) => false
            }
        }
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
