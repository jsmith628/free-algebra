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

impl<R,T:Add<Output=T>+AddAssociative> AssociativeAlgebraRule<R,T> for AddRule {}
impl<R,T:Add<Output=T>> AlgebraRule<R,T> for AddRule {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1+t2) }
}
impl<R,T:Add<Output=T>+Zero> UnitalAlgebraRule<R,T> for AddRule {
    fn one() -> T { T::zero() }
    fn is_one(t:&T) -> bool { t.is_zero() }
}

impl<R,T:Mul<Output=T>+MulAssociative> AssociativeAlgebraRule<R,T> for MulRule {}
impl<R,T:Mul<Output=T>> AlgebraRule<R,T> for MulRule {
    fn apply(t1:T, t2:T) -> (Option<R>,T) { (None, t1*t2) }
}
impl<R,T:Mul<Output=T>+One+PartialEq> UnitalAlgebraRule<R,T> for MulRule {
    fn one() -> T { T::one() }
    fn is_one(t:&T) -> bool { t.is_one() }
}

///
///A [FreeModule] over some monoid, but with a multiplication between elements given using the monoid operation
///
///# Examples
///```
///use maths_traits::algebra::*;
///use free_algebra::MonoidRing;
///
///#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
///pub enum SplitComplexUnit { One, J }
///
///impl MulAssociative for SplitComplexUnit {}
///impl MulCommutative for SplitComplexUnit {}
///impl Mul for SplitComplexUnit {
///    type Output = Self;
///    fn mul(self, rhs:Self) -> Self {
///        match self {
///            One => rhs,
///            J => match rhs {
///                One => J,
///                J => One,
///            }
///        }
///    }
///}
///
///impl maths_traits::algebra::One for SplitComplexUnit {
///    fn one() -> Self { One }
///    fn is_one(&self) -> bool { if let One=self { true } else { false } }
///}
///
///use SplitComplexUnit::*;
///type SplitComplex<R> = MonoidRing<R,SplitComplexUnit>;
///
///let x = SplitComplex::one() * 2.5 + SplitComplex::one() * (3.0, J);
///let y = SplitComplex::one() * 4.0 + SplitComplex::one() * (2.0, J);
///
///assert_eq!([x[&One], x[&J]], [2.5, 3.0]);
///assert_eq!([y[&One], y[&J]], [4.0, 2.0]);
///
///let z = x * y;
///assert_eq!([z[&One], z[&J]], [16.0, 17.0]);
///
///```
///
pub type MonoidRing<R,M> = ModuleString<R,M,MulRule>;

///
///A [module](RingModule) over a ring constructed from free addition scalar-multiplication of elements of a set
///
///Concretely, given a set `T` and ring `R`, we construct the free-module of `T` over `R` as
///the set of linear combination over elements in `T` where the scalars are in `R`. In practice,
///though, this construction is effectively just polynomials with variables from `T` but without
///multiplication.
///
///# Examples
///```
///use maths_traits::algebra::Zero;
///use free_algebra::FreeModule;
///
///let p = FreeModule::zero() + (3.5, 'x') + (2.0, 'y') + (1.0, 'x');
///let q = FreeModule::zero() - (1.5, 'x') + (2.0, 'y');
///
///assert_eq!([p[&'x'], p[&'y']], [4.5, 2.0]);
///assert_eq!([q[&'x'], q[&'y']], [-1.5, 2.0]);
///
///let r = &p + &q;
///let s = (p - q) * 0.5;
///
///assert_eq!([r[&'x'], r[&'y']], [3.0, 4.0]);
///assert_eq!([s[&'x'], s.get(&'y')], [3.0, 0.0]);
///
///```
///
pub type FreeModule<R,T> = ModuleString<R,T,!>;

///
///A [module](RingModule) over a ring constructed from free multiplication and addition of elements of a set
///
///Concretely, this is a [MonoidRing] of the [FreeMonoid] over `T` with coeffients in `R`. However,
///effectively, this just makes polynomials with elements of `T` as variables and coefficients in `R`,
///but where multiplication isn't commutative.
///
///# Examples
///```
///use maths_traits::algebra::One;
///use free_algebra::{FreeAlgebra, FreeMonoid};
///
///let one = FreeMonoid::one();
///let x:FreeMonoid<_> = 'x'.into();
///let y:FreeMonoid<_> = 'y'.into();
///
///let p = FreeAlgebra::<f32,_>::one() + &x;
///let q = FreeAlgebra::<f32,_>::one() - &y;
///
///assert_eq!([p[&one], p[&x]], [1.0, 1.0]);
///assert_eq!([q[&one], q[&y]], [1.0, -1.0]);
///
///let r = p * q;
///assert_eq!([r[&one], r[&x], r[&y], r[&(x*y)]], [1.0, 1.0, -1.0, -1.0]);
///
///```
///
pub type FreeAlgebra<R,T> = MonoidRing<R,FreeMonoid<T>>;
