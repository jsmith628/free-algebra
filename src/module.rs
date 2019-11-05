use super::*;

use std::collections::hash_map;


#[derive(Derivative)]
#[derivative(Clone(clone_from="true"))]
#[derivative(Default(bound=""))]
#[derivative(PartialEq, Eq, Hash)]
pub struct ModuleString<R,T:Hash+Eq,A:?Sized> {
    #[derivative(Hash(bound="HashMap<T,R>:Hash"))]
    #[derivative(Default(value="HashMap::with_capacity(0)"))]
    terms: HashMap<T,R>,

    #[derivative(PartialEq="ignore", Hash="ignore")]
    #[derivative(Debug="ignore")]
    rule: PhantomData<Box<A>>
}

///Iterates over references to the terms and coefficients of a [ModuleString]
pub type Iter<'a,R,T> = Map<hash_map::Iter<'a,T,R>, fn((&'a T,&'a R)) -> (&'a R,&'a T)>;

///Iterates over terms and coefficients of a [ModuleString]
pub type IntoIter<R,T> = Map<hash_map::IntoIter<T,R>, fn((T,R)) -> (R,T)>;

///
///Iterates over mutable references to the terms and coefficients of a [ModuleString]
///
///Note that this causes a reallocation of the internal [HashMap] since it's possible that an
///element mutation could create an illegal state if not reconstructed from the sums of the mutated
///terms. (For example, one could easily mutate two terms to have the same `T` value and thus
///potentially overwrite the coeffient of one of them if not handled properly)
///
pub struct IterMut<'a, R:AddAssign, T:Hash+Eq, A:?Sized> {
    dest_ref: &'a mut ModuleString<R,T,A>,
    next: Option<(R,T)>,
    iter: IntoIter<R,T>
}

impl<'a,T:Hash+Eq,R:AddAssign,A:?Sized> FusedIterator for IterMut<'a,R,T,A> {}
impl<'a,T:Hash+Eq,R:AddAssign,A:?Sized> ExactSizeIterator for IterMut<'a,R,T,A> {}
impl<'a,T:Hash+Eq,R:AddAssign,A:?Sized> Iterator for IterMut<'a,R,T,A> {
    type Item = (&'a mut R, &'a mut T);
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|t| *self.dest_ref += t);
        self.next = self.iter.next();

        //we know that the given reference is lifetime 'a because in order for next to be dropped,
        //either self must be borrowed mutably again or dropped, which cannot happen while the reference lives
        self.next.as_mut().map(|t| unsafe {&mut *(t as *mut (R,T))} ).map(|t| (&mut t.0, &mut t.1))
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a,T:Hash+Eq,R:AddAssign,A:?Sized> Drop for IterMut<'a,R,T,A> {
    fn drop(&mut self) {
        self.next.take().map(|t| *self.dest_ref += t);
        for t in &mut self.iter { *self.dest_ref += t }
    }
}

impl<T:Hash+Eq,R:One,A:?Sized> From<T> for ModuleString<R,T,A> {
    #[inline] fn from(t:T) -> Self {(R::one(),t).into()}
}

impl<T:Hash+Eq,R:One,A:?Sized> From<(R, T)> for ModuleString<R,T,A> {
    #[inline]
    fn from((r,t):(R,T)) -> Self {
        let mut m = HashMap::new();
        m.insert(t, r);
        ModuleString{terms:m, rule:PhantomData}
    }
}

impl<T:Hash+Eq,R,A:?Sized,I> Index<I> for ModuleString<R,T,A> where HashMap<T,R>:Index<I> {
    type Output = <HashMap<T,R> as Index<I>>::Output;
    #[inline] fn index(&self, i:I) -> &Self::Output {&self.terms[i]}
}

impl<T:Hash+Eq,R,A:?Sized> ModuleString<R,T,A> {
    ///Returns the number of terms in this module element
    pub fn num_terms(&self) -> usize {self.terms.len()}
}

impl<T:Hash+Eq,R,A:?Sized> IntoIterator for ModuleString<R,T,A> {
    type Item = (R,T);
    type IntoIter = IntoIter<R,T>;
    #[inline] fn into_iter(self) -> IntoIter<R,T> { self.terms.into_iter().map(|(t,r)| (r,t)) }
}

impl<T:Hash+Eq,R,A:?Sized> ModuleString<R,T,A> {
    ///Produces an iterator over references to the terms and references in this element
    pub fn iter<'a>(&'a self) -> Iter<'a,R,T> { self.terms.iter().map(|(t,r)| (r,t)) }

    ///Produces an iterator over mutable references to the terms and references in this element
    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a,R,T,A> where R:AddAssign {
        let mut temp = Self { terms: HashMap::with_capacity(self.terms.len()), rule:PhantomData };
        ::std::mem::swap(self, &mut temp);
        IterMut { dest_ref: self, next: None, iter: temp.into_iter() }
    }
}

impl<T:Hash+Eq,R,A:?Sized> ModuleString<R,T,A> {

    fn insert_term<F:Fn(&mut R, R)>(&mut self, rhs:(R,T), f:F) {
        if !rhs.0._is_zero() {
            let (r, t) = rhs;
            if let Some(r2) = self.terms.get_mut(&t) {
                f(r2,r);
                if r2._is_zero() { self.terms.remove(&t); }
            } else {
                self.terms.insert(t, r);
            }
        }
    }

    fn insert<I:IntoIterator<Item=(R,T)>, F:Fn(&mut R, R)+Copy>(&mut self, rhs:I, f:F) {
        rhs.into_iter().for_each(|term| self.insert_term(term, f));
    }

    ///removes all terms with a coeffient of zero
    fn clean(&mut self) { self.terms.retain(|r,_| !r._is_zero()); }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> Extend<(R,T)> for ModuleString<R,T,A> {
    fn extend<I:IntoIterator<Item=(R,T)>>(&mut self, iter:I) { self.insert(iter, |a,b| *a+=b) }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> FromIterator<(R,T)> for ModuleString<R,T,A> {
    fn from_iter<I:IntoIterator<Item=(R,T)>>(iter:I) -> Self {
        let mut from = Self::default();
        from.extend(iter);
        from
    }
}

impl<T:Hash+Eq,R:AddAssign+One,A:?Sized> FromIterator<T> for ModuleString<R,T,A> {
    fn from_iter<I:IntoIterator<Item=T>>(iter:I) -> Self {
        Self::from_iter(iter.into_iter().map(|t| (R::one(), t)))
    }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> FromIterator<Self> for ModuleString<R,T,A> {
    fn from_iter<I:IntoIterator<Item=Self>>(iter:I) -> Self {
        Self::from_iter(iter.into_iter().flatten())
    }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized,K> Sum<K> for ModuleString<R,T,A> where Self:FromIterator<K> {
    fn sum<I:Iterator<Item=K>>(iter:I) -> Self { Self::from_iter(iter) }
}

impl<T:Hash+Eq,R,A:?Sized,K> Product<K> for ModuleString<R,T,A> where Self:Mul<K,Output=Self>+One {
    fn product<I:Iterator<Item=K>>(iter:I) -> Self { iter.into_iter().fold(Self::one(), |m,k| m*k) }
}

///Dictates a rule for how to multiply terms in a [ModuleString]
pub trait AlgebraRule<R,T> {
    ///Multiplies two terms together to produce another `T` and an optional coeffient
    fn apply(t1:T, t2:T) -> (Option<R>,T);
}

///An [AlgebraRule] that is evaluation order independent
pub trait AssociativeAlgebraRule<R,T>: AlgebraRule<R,T> {}
///An [AlgebraRule] that is order independent
pub trait CommutativeMonoidRule<R,T>: AlgebraRule<R,T> {}

///An [AlgebraRule] where a term can be one
pub trait UnitalAlgebraRule<R,T>: AlgebraRule<R,T> {
    ///Creates a `T` with a value of one
    fn one() -> T;
    ///Determines if a `T` is equal to one
    fn is_one(t:&T) -> bool;
}

impl<T:Hash+Eq,R:AddAssociative,A:?Sized> AddAssociative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:AddCommutative,A:?Sized> AddCommutative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:MulAssociative,A:?Sized+AssociativeAlgebraRule<R,T>> MulAssociative for ModuleString<R,T,A> {}
impl<T:Hash+Eq,R:MulCommutative,A:?Sized+CommutativeMonoidRule<R,T>> MulCommutative for ModuleString<R,T,A> {}

impl<T:Hash+Eq,R:Distributive,A:?Sized> Distributive for ModuleString<R,T,A> {}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> AddAssign for ModuleString<R,T,A> {
    fn add_assign(&mut self, rhs:Self) {self.insert(rhs, |r1, r2| *r1+=r2)}
}
impl<T:Hash+Eq,R:SubAssign,A:?Sized> SubAssign for ModuleString<R,T,A> {
    fn sub_assign(&mut self, rhs:Self) {self.insert(rhs, |r1, r2| *r1-=r2)}
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> AddAssign<(R,T)> for ModuleString<R,T,A> {
    fn add_assign(&mut self, rhs:(R,T)) {self.insert_term(rhs, |r1, r2| *r1+=r2)}
}
impl<T:Hash+Eq,R:SubAssign,A:?Sized> SubAssign<(R,T)> for ModuleString<R,T,A> {
    fn sub_assign(&mut self, rhs:(R,T)) {self.insert_term(rhs, |r1, r2| *r1-=r2)}
}

impl<T:Hash+Eq,R:AddAssign+One,A:?Sized> AddAssign<T> for ModuleString<R,T,A> {
    fn add_assign(&mut self, rhs:T) {*self+=(R::one(),rhs)}
}
impl<T:Hash+Eq,R:SubAssign+One,A:?Sized> SubAssign<T> for ModuleString<R,T,A> {
    fn sub_assign(&mut self, rhs:T) {*self-=(R::one(),rhs)}
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
            terms: self.terms.into_iter().map(|(t,r)| (t,-r)).filter(|(_,r)| r._is_zero()).collect(),
            rule: PhantomData
        }
    }
}

impl<T:Hash+Eq,R:AddAssign,A:?Sized> Zero for ModuleString<R,T,A> {
    #[inline] fn zero() -> Self {Default::default()}
    #[inline] fn is_zero(&self) -> bool {self.terms.len()==0}
}

impl<T:Clone+Hash+Eq,R:PartialEq+UnitalSemiring,A:UnitalAlgebraRule<R,T>+?Sized> One for ModuleString<R,T,A> {
    #[inline] fn one() -> Self { A::one().into() }
    #[inline] fn is_one(&self) -> bool {
        if self.terms.len()==1 {
            let term = self.iter().next().unwrap();
            term.0.is_one() && A::is_one(term.1)
        } else {
            false
        }
    }
}


impl<T:Hash+Eq+Clone,R:MulMagma,A:?Sized+AlgebraRule<R,T>> MulAssign<(R,T)> for ModuleString<R,T,A> {
    fn mul_assign(&mut self, (r1,t1): (R,T)) {
        let mut temp = HashMap::with_capacity(0);
        ::std::mem::swap(&mut self.terms, &mut temp);
        self.terms = temp.into_iter().map(
            |(t, r)| {
                let (coeff, t2) = A::apply(t, t1.clone());
                match coeff {
                    Some(r2) => (t2, (r*r1.clone())*r2),
                    None => (t2, r*r1.clone()),
                }
            }
        ).filter(|(_,r)| r._is_zero()).collect();
    }
}

impl<T:Hash+Eq+Clone,R:Semiring,A:?Sized+AlgebraRule<R,T>> MulAssign for ModuleString<R,T,A> {
    fn mul_assign(&mut self, rhs:Self) {
        *self = rhs.terms.into_iter().map(|(t, r)| self.clone() * (r,t)).sum();
    }
}

impl<Z,R,T,A> Pow<Z> for ModuleString<R,T,A> where
    Z:Natural,
    T:Hash+Eq+Clone,
    R:PartialEq+UnitalSemiring,
    A:?Sized+UnitalAlgebraRule<R,T>+AssociativeAlgebraRule<R,T>
{
    type Output = Self;
    fn pow(self, p:Z) -> Self { repeated_squaring(self, p) }
}
