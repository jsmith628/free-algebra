#![feature(specialization)]
#![feature(marker_trait_attr)]
#![feature(never_type)]

#[macro_use] extern crate derivative;
extern crate num_traits;
extern crate maths_traits;

pub use self::monoid::*;
pub use self::module::*;

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

macro_rules! from_assign {

    (impl<$($T:ident),*> $Trait:ident<$RHS:ident>.$fun:ident for $ty:ident<$($U:ident),*> with $op:tt $($where:tt)*) => {
        impl<$($T),*> $Trait<$RHS> for $ty<$($U),*> $($where)* {
            type Output = Self;
            #[inline] fn $fun(mut self, rhs:$RHS) -> Self {self $op rhs; self}
        }
    }

}

pub(self) fn map_hash<K:Hash+Eq,V:Hash, H:Hasher>(map: &HashMap<K,V>, state: &mut H) {
    use std::num::Wrapping;
    use std::collections::hash_map::DefaultHasher;

    let mut hash = Wrapping(0u64);
    let mut start = true;
    for (k,v) in map.iter(){
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

mod monoid;
mod module;
