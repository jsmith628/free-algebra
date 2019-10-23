
use maths_traits::algebra::*;

use std::marker::PhantomData;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

pub struct ModuleString<R,T:Hash+Eq,A:?Sized> {
    terms: HashMap<T,R>,
    rule: PhantomData<Box<A>>
}

impl<T:Hash+Eq+Clone,R:Clone,A:?Sized> Clone for ModuleString<R,T,A> {
    #[inline] fn clone(&self) -> Self { ModuleString {terms: self.terms.clone(), rule: PhantomData} }
}

impl<T:Hash+Eq+Clone,R:Eq,A:?Sized> Eq for ModuleString<R,T,A> {}
impl<T:Hash+Eq+Clone,R:PartialEq,A:?Sized> PartialEq for ModuleString<R,T,A> {
    #[inline] fn eq(&self, rhs:&Self) -> bool {self.terms.eq(&rhs.terms)}
    #[inline] fn ne(&self, rhs:&Self) -> bool {self.terms.ne(&rhs.terms)}
}

impl<T:Hash+Eq,R:Hash,A:?Sized> Hash for ModuleString<R,T,A> {
    fn hash<H:Hasher>(&self, state: &mut H) {
        use std::num::Wrapping;
        use std::collections::hash_map::DefaultHasher;

        let mut hash = Wrapping(0u64);
        let mut start = true;
        for (k,v) in self.terms.iter(){
            //hash the key-value pair
            let mut d = DefaultHasher::new();
            (k,v).hash(&mut d);
            let next = Wrapping(d.finish());

            //now, compose the hash with the main hash using multiplication
            //since that is commutative
            hash = if start {next} else {hash * next};
            start = false;
        }
        state.write_u64(hash.0)
    }
}

impl<T:Hash+Eq,R,A:?Sized> Default for ModuleString<R,T,A> {
    #[inline] fn default() -> Self {ModuleString{terms:HashMap::new(),rule:PhantomData}}
}

impl<T:Hash+Eq,R:One,A:?Sized> From<T> for ModuleString<R,T,A> { #[inline] fn from(t:T) -> Self {(R::one(),t).into()} }
impl<T:Hash+Eq,R:One,A:?Sized> From<(R, T)> for ModuleString<R,T,A> {
    #[inline] fn from((r,t):(R,T)) -> Self {
        let mut m = HashMap::new();
        m.insert(t, r);
        ModuleString{terms:m, rule:PhantomData}
    }
}

impl<T:Hash+Eq,R,A:?Sized> AsRef<HashMap<T,R>> for ModuleString<R,T,A> {
    #[inline] fn as_ref(&self) -> &HashMap<T,R> {&self.terms}
}
impl<T:Hash+Eq,R,A:?Sized,I> Index<I> for ModuleString<R,T,A> where HashMap<T,R>:Index<I> {
    type Output = <HashMap<T,R> as Index<I>>::Output;
    #[inline] fn index(&self, i:I) -> &Self::Output {&self.terms[i]}
}

impl<T:Hash+Eq,R,A:?Sized> ModuleString<R,T,A> {
    pub fn terms(&self) -> usize {self.terms.len()}
}

impl<T:Hash+Eq,R,A:?Sized> IntoIterator for ModuleString<R,T,A> {
    type Item = <HashMap<T,R> as IntoIterator>::Item;
    type IntoIter = <HashMap<T,R> as IntoIterator>::IntoIter;
    #[inline] fn into_iter(self) -> Self::IntoIter { self.terms.into_iter() }
}

pub trait AlgebraRule<R,T> { fn apply(t1:T, t2:T) -> (Option<R>,T); }

impl<T:Hash+Eq,R:AddAssociative,A:?Sized> AddAssociative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:AddCommutative,A:?Sized> AddCommutative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:MulAssociative,A:?Sized+MulAssociative> MulAssociative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:MulCommutative,A:?Sized+MulCommutative> MulCommutative for ModuleString<R,T,A> {}

impl<T:Hash+Eq,R:Distributive,A:?Sized> Distributive for ModuleString<R,T,A> {}

trait Clean { fn clean(&mut self); }

impl<T:Hash+Eq,R,A:?Sized> Clean for ModuleString<R,T,A> { default fn clean(&mut self) {} }
impl<T:Hash+Eq,R:Zero,A:?Sized> Clean for ModuleString<R,T,A> {
    default fn clean(&mut self) {self.terms.retain(|_,r| !r.is_zero())}
}

impl<T:Hash+Eq,R,A:?Sized> ModuleString<R,T,A> {
    fn insert<F:Fn(&mut R, R)>(&mut self, rhs:Self, f:F) {
        for (t, r) in rhs.terms.into_iter() {
            if let Some(r2) = self.terms.get_mut(&t) {
                f(r2,r);
                continue;
            }
            self.terms.insert(t, r);
        }
        self.clean();
    }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> AddAssign for ModuleString<R,T,A> {
    fn add_assign(&mut self, rhs:Self) {self.insert(rhs, |r1, r2| *r1+=r2)}
}
impl<T:Hash+Eq,R:SubAssign,A:?Sized> SubAssign for ModuleString<R,T,A> {
    fn sub_assign(&mut self, rhs:Self) {self.insert(rhs, |r1, r2| *r1-=r2)}
}
impl<T:Hash+Eq,R:MulAssign+Clone,A:?Sized> MulAssign<R> for ModuleString<R,T,A> {
    fn mul_assign(&mut self, rhs:R) {
        for r2 in self.terms.values_mut() { *r2 *= rhs.clone() }
        self.clean();
    }
}
impl<T:Hash+Eq,R:DivAssign+Clone,A:?Sized> DivAssign<R> for ModuleString<R,T,A> {
    fn div_assign(&mut self, rhs:R) {
        for r2 in self.terms.values_mut() { *r2 /= rhs.clone() }
        self.clean();
    }
}

from_assign!(impl<T,R,A,X> Add<X>.add for ModuleString<R,T,A> with += where T:Hash+Eq, A:?Sized, Self:AddAssign<X>);
from_assign!(impl<T,R,A,X> Sub<X>.sub for ModuleString<R,T,A> with -= where T:Hash+Eq, A:?Sized, Self:SubAssign<X>);
from_assign!(impl<T,R,A,X> Mul<X>.mul for ModuleString<R,T,A> with *= where T:Hash+Eq, A:?Sized, Self:MulAssign<X>);
from_assign!(impl<T,R,A,X> Div<X>.div for ModuleString<R,T,A> with /= where T:Hash+Eq, A:?Sized, Self:DivAssign<X>);

impl<T:Hash+Eq,R:Neg,A:?Sized> Neg for ModuleString<R,T,A> {
    type Output = ModuleString<R::Output,T,A>;
    fn neg(self) -> Self::Output {
        ModuleString {
            terms: self.terms.into_iter().map(|(t,r)| (t,-r)).collect(),
            rule: PhantomData
        }
    }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> Zero for ModuleString<R,T,A> {
    #[inline] fn zero() -> Self {Default::default()}
    #[inline] fn is_zero(&self) -> bool {self.terms.len()==0}
}


impl<T:Hash+Eq+Clone,R:MulMagma,A:?Sized+AlgebraRule<R,T>> MulAssign<(R,T)> for ModuleString<R,T,A> {
    fn mul_assign(&mut self, (r1,t1): (R,T)) {
        let mut temp = HashMap::new();
        ::std::mem::swap(&mut self.terms, &mut temp);
        self.terms = temp.into_iter().map(
            |(t, r)| {
                let (coeff, t2) = A::apply(t, t1.clone());
                match coeff {
                    Some(r2) => (t2, (r*r1.clone())*r2),
                    None => (t2, r*r1.clone()),
                }
            }
        ).collect();
        self.clean();
    }
}

impl<T:Hash+Eq+Clone,R:Semiring,A:?Sized+AlgebraRule<R,T>> MulAssign for ModuleString<R,T,A> {
    fn mul_assign(&mut self, rhs:Self) {
        let res = rhs.terms.into_iter().map(
            |(t, r)| self.clone() * (r,t)
        ).fold(Self::zero(),
            |res, p| res + p
        );
        self.terms = res.terms;
    }
}







pub type FreeModule<R,T> = ModuleString<R,T,()>;
