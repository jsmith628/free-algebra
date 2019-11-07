use super::*;

pub use self::free_monoid::*;
pub use self::free_group::*;
pub use self::free_pow::*;

mod free_monoid;
mod free_group;
mod free_pow;

///Multiplication of terms using a type's intrinsic [addition](Add) operation
pub struct AddRule;
///Multiplication of terms using a type's intrinsic [multiplication](Mul) operation
pub struct MulRule;

impl<R,T:Add<Output=T>> AlgebraRule<R,T> for AddRule {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1+t2) }
}
impl<R,T:Add<Output=T>+Zero> UnitalAlgebraRule<R,T> for AddRule {
    fn one() -> T { T::zero() }
    fn is_one(t:&T) -> bool { t.is_zero() }
}

impl<R,T:Mul<Output=T>> AlgebraRule<R,T> for MulRule {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1*t2) }
}
impl<R,T:Mul<Output=T>+One+PartialEq> UnitalAlgebraRule<R,T> for MulRule {
    fn one() -> T { T::one() }
    fn is_one(t:&T) -> bool { t.is_one() }
}

///A [FreeModule] over some monoid, but with a multiplication between elements given using the monoid operation
pub type MonoidRing<R,M> = ModuleString<R,M,MulRule>;

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
