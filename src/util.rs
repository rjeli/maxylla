use std::{cmp::Eq, collections::HashMap, hash::Hash};

pub fn insert_or_append<A: Eq + Hash + Clone, B>(m: &mut HashMap<A, Vec<B>>, key: &A, val: B) {
    if !m.contains_key(key) {
        m.insert(key.clone(), vec![]);
    }
    m.get_mut(key).unwrap().push(val);
}
