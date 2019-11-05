use super::*;

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

///
///Represents a free symbol raised to some integral power
///
///This meant to provide a way to invert a symbol so that is can be used to construct the [FreeGroup]
///type and to save space in free-monoids that may have many repeated symbols
///
#[derive(Derivative)]
#[derivative(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct FreePow<C:Eq,Z:IntegerSubset>(pub C,pub Z);

///Provides multiplication between [FreeGroup] elements using addition of exponents on equal bases
pub struct PowRule;

impl<C:Eq,Z:IntegerSubset> AssociativeMonoidRule<FreePow<C,Z>> for PowRule {}
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

///
///A [monoid](MulMonoid) constructed from free multiplication (or addition) of elements of a set
///
///Concretely, given a set `C`, we construct the free-monoid of `C` as the set of all finite lists
///of members of `C` where multiplication is given by concatenation. In other words, it's basically
///[`Vec<C>`](Vec) but with `a*b == {a.append(&mut b); a}`.
///
pub type FreeMonoid<C> = MonoidalString<C,(),()>;

///A [FreeMonoid], but where each element can be symbolically inverted
pub type FreeGroup<C,Z> = MonoidalString<FreePow<C,Z>,!,PowRule>;


///Provides multiplication of terms via the type's intrinsic [addition](Add) operation
pub struct RuleFromAdd;
///Provides multiplication of terms via the type's intrinsic [multiplication](Mul) operation
pub struct RuleFromMul;

impl<R,T:Add<Output=T>> AlgebraRule<R,T> for RuleFromAdd {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1+t2) }
}
impl<R,T:Add<Output=T>+Zero> UnitalAlgebraRule<R,T> for RuleFromAdd {
    fn one() -> T { T::zero() }
    fn is_one(t:&T) -> bool { t.is_zero() }
}

impl<R,T:Mul<Output=T>> AlgebraRule<R,T> for RuleFromMul {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1*t2) }
}
impl<R,T:Mul<Output=T>+One+PartialEq> UnitalAlgebraRule<R,T> for RuleFromMul {
    fn one() -> T { T::one() }
    fn is_one(t:&T) -> bool { t.is_one() }
}

///A [FreeModule] over some monoid, but with a multiplication between elements given using the monoid operation
pub type MonoidRing<R,M> = MonoidalString<R,M,RuleFromMul>;

///
///A [module](RingModule) over a ring constructed from free addition scalar-multiplication of elements of a set
///
///Concretely, given a set `T` and ring `R`, we construct the free-module of `T` over `R` as
///the set of linear combination over elements in `T` where the scalars are in `R`.
///
pub type FreeModule<R,T> = ModuleString<R,T,!>;

///
///A [module](RingModule) over a ring constructed from free multiplication and addition of elements of a set
///
///Concretely, this is a [MonoidRing] over `R` of the [FreeMonoid] over `T`. However, this is
///effectively just the set of polynomials with coeffients in `R` where the variables are all the
///elements of `T` (and where we don't assume associativity or commutivity of the
///variables).
///
pub type FreeAlgebra<R,T> = MonoidRing<R,FreeMonoid<T>>;
