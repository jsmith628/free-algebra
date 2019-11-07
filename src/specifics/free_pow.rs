use super::*;

///A [FreeModule] or [FreeGroup], but where repeated letters are grouped together using exponents
pub type FreePowMonoid<C,P> = MonoidalString<FreePow<C,P>,PowRule>;

///
///Represents a free symbol raised to some power
///
///This is used in [FreePowMonoid] mainly as a way to compress the size-footprint of a
///[FreeMonoid] by combining repeated elements under an integral exponent, but the option for more
///exotic exponents is also available
///
#[derive(Derivative)]
#[derivative(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct FreePow<C:Eq,P>(pub C,pub P);

impl<C:Eq+Display,P:Display> Display for FreePow<C,P> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{}^{}", self.0, self.1)
    }
}

impl<C:Eq,P:One+Neg<Output=P>> From<FreeInv<C>> for FreePow<C,P> {
    fn from(inv: FreeInv<C>) -> Self {
        match inv {
            FreeInv::Id(x) => FreePow(x,P::one()),
            FreeInv::Inv(x) => FreePow(x,-P::one()),
        }
    }
}

///Multiplication between [FreePow] elements using addition of exponents on equal bases
pub struct PowRule;

impl<C:Eq,P:Add<Output=P>+AddAssociative> AssociativeMonoidRule<FreePow<C,P>> for PowRule {}
impl<C:Eq,P:Add<Output=P>> MonoidRule<FreePow<C,P>> for PowRule {
    fn apply(mut string: Vec<FreePow<C,P>>, letter: FreePow<C,P>) -> Vec<FreePow<C,P>> {
        if string.last().map_or(false, |l| l.0==letter.0) {
            let last = string.pop().unwrap();
            let last = FreePow(letter.0, last.1 + letter.1);
            if !last.1._is_zero() { string.push(last); }
        } else {
            string.push(letter);
        }
        string
    }
}

impl<C:Eq,P:Add<Output=P>+Neg<Output=P>> InvMonoidRule<FreePow<C,P>> for PowRule {
    fn invert(free: FreePow<C,P>) -> FreePow<C,P> { free.inv() }
}

impl<C:Eq,P:One> From<C> for FreePow<C,P> { fn from(c:C) -> Self { (c,P::one()).into() } }
impl<C:Eq,P> From<(C,P)> for FreePow<C,P> { fn from((c,z):(C,P)) -> Self { FreePow(c,z) } }

impl<C:Eq,P:Neg<Output=P>> Inv for FreePow<C,P> {
    type Output = Self;
    fn inv(self) -> Self { FreePow(self.0, -self.1) }
}

impl<C:Eq,P:Add<Output=P>> Mul for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn mul(self, rhs:Self) -> FreePowMonoid<C,P> { FreePowMonoid::from(self) * rhs }
}

impl<C:Eq,P:Add<Output=P>+One> Mul<C> for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn mul(self, rhs:C) -> FreePowMonoid<C,P> { self * Self::from(rhs) }
}

impl<C:Eq,P:Add<Output=P>> Mul<FreePowMonoid<C,P>> for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn mul(self, rhs:FreePowMonoid<C,P>) -> FreePowMonoid<C,P> { FreePowMonoid::from(self) * rhs }
}

impl<C:Eq,P:Add<Output=P>+Neg<Output=P>> Div for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn div(self, rhs:Self) -> FreePowMonoid<C,P> { self * rhs.inv() }
}

impl<C:Eq,P:Add<Output=P>+One+Neg<Output=P>> Div<C> for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn div(self, rhs:C) -> FreePowMonoid<C,P> { self / Self::from(rhs) }
}

impl<C:Eq,P:Add<Output=P>+Neg<Output=P>> Div<FreePowMonoid<C,P>> for FreePow<C,P> {
    type Output = FreePowMonoid<C,P>;
    fn div(self, rhs:FreePowMonoid<C,P>) -> FreePowMonoid<C,P> { FreePowMonoid::from(self) / rhs }
}
