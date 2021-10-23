
#![allow(unused)]

use std::fmt::Debug;
use std::mem::{replace, take};

use crate::arr::*;
use crate::if_good::*;

use Node::*;



#[derive(Debug)]
pub enum Node<K, const M: usize, const N: usize> {
    Seed,
    Branch { keys: Arr<K, M>, child: Arr<Node<K, M, N>, N> },
    Leaf   { keys: Arr<K, M>                               },
}

impl<K, const M: usize, const N: usize> Node<K, M, N> 
where
    K: Debug + Default + Ord,
{
    fn n_keys(&self) -> usize {
        match self {
            Branch { keys, child } => keys.len(),
            Leaf   { keys        } => keys.len(),
            Seed                   => 0,
        }
    }
    fn pop_key(&mut self) -> Option<K> {
        match self {
            Branch { keys, child } => keys.pop(),
            Leaf   { keys        } => keys.pop(),
            Seed                   => None,
        }
    }
    fn full(&self) -> bool {
        match self {
            Branch { keys, child } => keys.full(),
            Leaf   { keys        } => keys.full(),
            Seed                   => false,
        }
    }
    fn take(&mut self) -> Self {
        take(self)
    }
    fn traverse(&self) {
        match self {
            Branch { keys, child } => {
                keys.into_iter().zip(child)
                    .for_each(|(k, c)| { 
                        c.traverse(); 
                        println!("{:?}", k);
                    });
                child.last().if_some(|ch| ch.traverse());
            },
            Leaf { keys } => {
                keys.into_iter().for_each(|k| println!("{:?}", k));
            }
            seed => { },
        }
    }
    fn search(&self, k: &K) -> Option<&K> {
        match self {
            Branch { keys, child } => {
                keys.binary_search(k)
                    .map_or_else(|i| child[i].search(k),
                                 |i| Some(&keys[i]))
            },
            Leaf { keys } => {
                keys.binary_search(k).map(|i| &keys[i]).ok()
            },
            Seed => None,
        }
    }
    fn insert(&mut self, k: K) {
        match self {
            Branch { keys, child } => {
                match keys.binary_search(&k) {
                    Err(i) => {
                        if child[i].full() {
                            let ch = child[i].split();
                            child.insert(i + 1, ch);
                            child[i].pop_key().if_some(|k| keys.insert(i, k));
                        }
                        child[i].insert(k);
                    }, 
                    Ok(i) => { keys[i] = k; }
                }
            },
            Leaf { keys } => {
                match keys.binary_search(&k) {
                    Err(i) => { keys.insert(i, k); },
                    Ok(i)  => { keys[i] = k;       },
                }
            },
            Seed => { 
                let mut keys = Arr::new();
                keys.push(k);
                *self = Leaf { keys };
            },
        }
    }
    fn split(&mut self) -> Node<K, M, N> {
        match self {
            Branch { keys, child } => {
                let mut k2 = keys.split();
                let mut c2 = child.split();
                Branch { keys: k2, child: c2 }
            },
            Leaf { keys } => {
                let mut k2 = keys.split();
                Leaf { keys: k2 }
            },
            Seed => panic!("Can't split a Seed."),
        }
    }
    fn remove(&mut self, k: &K) -> Option<K> {
        match self {
            Branch { keys, child } => {
                match keys.binary_search(k) {
                    Ok(i) => {
                        if child[i].n_keys() >= M / 2 {
                            let pred = child[i].max_key();
                            Some(replace(&mut keys[i], pred))
                        } 
                        else if child[i + 1].n_keys() >= M / 2 {
                            let succ = child[i + 1].min_key();
                            Some(replace(&mut keys[i], succ))
                        } 
                        else {
                            let c = child.remove(i + 1);
                            let k = keys.remove(i);
                            child[i].merge(c);
                            if keys.len() == 0 {
                                *self = child.remove(i);
                            }
                            Some(k)
                        }
                    },
                    Err(i) => {
                        child[i].remove(k)
                    },
                }
            },
            Leaf { keys } => {
                keys.binary_search(k).map(|i| keys.remove(i)).ok()
            },
            Seed => None,
        }
    }
    fn merge(&mut self, mut other: Node<K, M, N>) {
        match (self, other) {
            (Branch { keys: k1, child: c1 }, 
             Branch { keys: k2, child: c2 }) => {
                k1.merge(k2);
                c1.merge(c2);
             },
             (Leaf { keys: k1 }, Leaf { keys: k2 }) => {
                k1.merge(k2);
             },
            _ => panic!("Invalid operands for Node::merge()."),
        }
    }
    fn max_key(&mut self) -> K {
        let mut curr = self; 
        let mut key  = None;
        loop {
            match curr {
                Branch { keys, child } => {
                    curr = child.last_mut().unwrap();
                },
                Leaf { keys } => { key = keys.pop(); break; },
                Seed => { break; }
            }
        }
        key.unwrap()
    }
    fn min_key(&mut self) -> K {
        let mut curr = self;
        let mut key  = None;
        loop {
            match curr {
                Branch { keys, child } => {
                    curr = &mut child[0];
                },
                Leaf { keys } => { key = Some(keys.remove(0)); break; },
                Seed => { break; }
            }
        }
        key.unwrap()
    }
}
impl<K, const M: usize, const N: usize> Default for Node<K, M, N> {
    fn default() -> Self {
        Seed
    }
}

#[derive(Debug)]
pub struct BTree<K, const M: usize, const N: usize> {
    root  : Node<K, M, N>,
}

impl<K, const M: usize, const N: usize> BTree<K, M, N> 
where
    K: Debug + Default + Ord,
{
    pub fn new() -> Self {
        Self { root: Seed }
    }
    pub fn with_order(d: usize) -> Self {
        Self { root: Seed }
    }
    fn traverse(&self) {
        self.root.traverse();
    }
    pub fn search(&self, k: &K) -> Option<&K> {
        self.root.search(k)
    }
    pub fn insert(&mut self, k: K) {
        if self.root.full() {
            let mut ch1   = self.root.take();
            let mut ch2   = ch1.split();
            let mut keys  = Arr::new();
            let mut child = Arr::new();
            let     key   = ch1.pop_key().unwrap();
            
            if k < key { ch1.insert(k); } 
            else       { ch2.insert(k); }
            
            keys.push(key);
            child.push(ch1);
            child.push(ch2);
            
            self.root = Branch { keys, child };
        } else {
            self.root.insert(k);
        }
    }
    pub fn remove(&mut self, k: &K) -> Option<K> {
        let key = self.root.remove(k);
        if self.root.n_keys() == 0 {
            self.root = Seed;
        }
        key
    }
}

impl<K, const M: usize, const N: usize> Default for BTree<K, M, N> 
where
    K: Debug + Default + Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

pub fn btree_order_3<K>() -> BTree<K, 6, 7> 
where
    K: Debug + Default + Ord,
{
    BTree::<K, 6, 7>::new()
}

#[cfg(test)]
mod tests {
    use crate::btree::*;
    
    #[test]
    fn insert() {
        let mut t = btree_order_3(); // A B-Tree with minimum order 3
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n);
        }
        t.traverse();
        println!("{:#?}", t);
    }
    #[test] 
    fn remove() {
        let mut t = btree_order_3();
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n);
        }
        /* t.remove(&6);
           t.remove(&7);
           t.remove(&5); */
        t.remove(&10);
        t.remove(&7);
        t.remove(&12);
        t.remove(&17);
        println!("{:#?}", t);
    }
    
    #[test]
    fn search() {
        let mut t = btree_order_3();
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n);
        }
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            assert_eq!(t.search(&n), Some(&n));
        }
        for n in [18, 2, 9, 42, 100] {
            assert_eq!(t.search(&n), None);
        }
    }
}
