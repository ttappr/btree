
#![allow(unused)]

use std::fmt::Debug;
use std::mem::{replace, take};

use crate::arr::*;

const ORDER     : usize = 3;
const MAX_KEY   : usize = ORDER * 2;
const MAX_CHILD : usize = ORDER * 2 + 1;

use Node::*;



#[derive(Debug)]
pub enum Node<K> {
    Seed,
    Branch { keys: Arr<K, MAX_KEY>, child: Arr<Node<K>, MAX_CHILD> },
    Leaf   { keys: Arr<K, MAX_KEY>                                 },
}

impl<K> Node<K> 
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
    fn full(&self, d: usize) -> bool {
        self.n_keys() >= 2 * d - 1
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
                child.last().map(|ch| ch.traverse());
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
    fn insert(&mut self, k: K, d: usize) {
        match self {
            Branch { keys, child } => {
                match keys.binary_search(&k) {
                    Err(i) => {
                        if child[i].full(d) {
                            let ch = child[i].split(d);
                            child.insert(i + 1, ch);
                            child[i].pop_key().map(|k| keys.insert(i, k));
                        }
                        child[i].insert(k, d);
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
    fn split(&mut self, d: usize) -> Node<K> {
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
    fn remove(&mut self, k: &K, d: usize) -> Option<K> {
        match self {
            Branch { keys, child } => {
                match keys.binary_search(k) {
                    Ok(i) => {
                        if child[i].n_keys() >= d {
                            let pred = child[i].max_key();
                            Some(replace(&mut keys[i], pred))
                        } 
                        else if child[i + 1].n_keys() >= d {
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
                        child[i].remove(k, d)
                    },
                }
            },
            Leaf { keys } => {
                keys.binary_search(k).map(|i| keys.remove(i)).ok()
            },
            Seed => None,
        }
    }
    fn merge(&mut self, mut other: Node<K>) {
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
impl<K> Default for Node<K> {
    fn default() -> Self {
        Seed
    }
}

#[derive(Debug)]
pub struct BTree<K> {
    order : usize,
    root  : Node<K>,
}

impl<K> BTree<K> 
where
    K: Debug + Default + Ord,
{
    pub fn new() -> Self {
        Self { order: ORDER, root: Seed }
    }
    pub fn with_order(d: usize) -> Self {
        Self { order: d, root: Seed }
    }
    fn traverse(&self) {
        self.root.traverse();
    }
    pub fn search(&self, k: &K) -> Option<&K> {
        self.root.search(k)
    }
    pub fn insert(&mut self, k: K) {
        if self.root.full(self.order) {
            let mut ch1   = self.root.take();
            let mut ch2   = ch1.split(self.order);
            let mut keys  = Arr::new();
            let mut child = Arr::new();
            let     key   = ch1.pop_key().unwrap();
            
            if k < key { ch1.insert(k, self.order); } 
            else       { ch2.insert(k, self.order); }
            
            keys.push(key);
            child.push(ch1);
            child.push(ch2);
            
            self.root = Branch { keys, child };
        } else {
            self.root.insert(k, self.order);
        }
    }
    pub fn remove(&mut self, k: &K) -> Option<K> {
        let key = self.root.remove(k, self.order);
        if self.root.n_keys() == 0 {
            self.root = Seed;
        }
        key
    }
}



#[cfg(test)]
mod tests {
    use crate::btree::*;
    
    #[test]
    fn insert() {
        let mut t = BTree::with_order(3); // A B-Tree with minimum order 3
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n);
        }
        t.traverse();
        println!("{:#?}", t);
    }
    #[test] 
    fn remove() {
        let mut t = BTree::with_order(3);
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
        let mut t = BTree::with_order(3); // A B-Tree with minimum order 3
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
