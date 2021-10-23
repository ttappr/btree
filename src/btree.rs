
#![allow(unused)]

use std::fmt::Debug;
use std::mem::{replace, take};

use crate::arr::*;
use crate::if_good::*;

use Node::*;


/// The node type of the tree. The 'order' of the tree is defined as the minimum
/// number of keys that can populate a node. The maximum number of keys (`M`) 
/// must be 'order' * 2, and the maximum number of children (`N`) must be 
/// 'order' * 2 + 1.
/// 
/// The 'order' of the tree can be considerably large (up to 128) as the 
/// operations on the internal array of the node use binary search to locate
/// keys.
/// 
/// # Variants
/// * `Seed`    - Represents an empty node.
/// * `Branch`  - A non-terminal node.
/// * `Leaf`    - A terminal node.
/// 
/// # Generic Parameters
/// * `K`   - The key type.
/// * `M`   - The maximum number of keys (must be 'order' * 2).
/// * `N`   - The maximum number of children (must be 'order' * 2 + 1).
/// 
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
    /// Returns the number of keys in the node.
    /// 
    fn n_keys(&self) -> usize {
        match self {
            Branch { keys, child } => keys.len(),
            Leaf   { keys        } => keys.len(),
            Seed                   => 0,
        }
    }

    /// Pops and returns the last key of the node if any keys are present.
    /// 
    fn pop_key(&mut self) -> Option<K> {
        match self {
            Branch { keys, child } => keys.pop(),
            Leaf   { keys        } => keys.pop(),
            Seed                   => None,
        }
    }

    /// Reports whether the node has reached the maximum key population.
    /// 
    fn full(&self) -> bool {
        match self {
            Branch { keys, child } => keys.full(),
            Leaf   { keys        } => keys.full(),
            Seed                   => false,
        }
    }

    /// Returns the node, replacing `self` with the `Seed` variant.
    /// 
    fn take(&mut self) -> Self {
        take(self)
    }

    /// For debugging during development. Prints out the tree.
    /// 
    fn traverse(&self) {
        match self {
            Branch { keys, child } => {
                keys.into_iter().zip(child)
                    .for_each(|(k, c)| { 
                        c.traverse(); 
                        println!("{:?}", k);
                    });
                child.last().if_some(Self::traverse);
            },
            Leaf { keys } => {
                keys.into_iter().for_each(|k| println!("{:?}", k));
            }
            seed => { },
        }
    }

    /// Returns a reference to the key matching `k` if it exists in the tree;
    /// otherwise `None` is returned. Uses a combination of tree traversal,
    /// to navigate to the right node, then binary search to locate the key
    /// within the node's internal array. This enables the 'order' of the tree
    /// to be considerably large without sacrificing performance.
    /// 
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

    /// Inserts the given key into the tree, or updates the existing matching
    /// key.
    /// 
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

    /// Splits a node in half, returning a new node containing the larger keys.
    /// 
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

    /// Removes the key that matches `k` from the tree and returns it if it
    /// exists; otherwise `None` is returned. The tree automatically rebalances.
    /// 
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

    /// Combines the current node with `other`. The nodes must be of the same
    /// variant.
    /// 
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

    /// Descends the tree from the current node to find it's maximum key.
    /// This key is removed from its hosting node and returned.
    /// 
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

    /// Descends the tree from the current node to find that branch's minimum
    /// key. The key is removed from the tree and returned.
    /// 
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

    /// Returns the default value for `Node`, which is the variant `Seed`.
    /// 
    fn default() -> Self {
        Seed
    }
}

/// The main class for the tree. Holds the root node.
/// 
/// # Generic Parameters
/// * `K`   - The key type.
/// * `M`   - The maximum number of keys of a node (must be 'order' * 2).
/// * `N`   - The maximum number of children of any node 
///           (must be 'order' * 2 + 1).
/// 
#[derive(Debug)]
pub struct BTree<K, const M: usize, const N: usize> {
    root  : Node<K, M, N>,
}

impl<K, const M: usize, const N: usize> BTree<K, M, N> 
where
    K: Debug + Default + Ord,
{
    /// Returns a new `BTree` with a `Seed` as root.
    /// 
    pub fn new() -> Self {
        Self { root: Seed }
    }

    /// A temporary method to traverse the tree and print out the nodes. To
    /// be removed at some point.
    /// TODO - When removing this, also remove the `Debug` constraint on `K`.
    /// 
    fn traverse(&self) {
        self.root.traverse();
    }

    /// Locates the key that matches `k` and returns a reference to it if it
    /// exists within the tree; `None` is returned otherwise.
    /// 
    pub fn search(&self, k: &K) -> Option<&K> {
        self.root.search(k)
    }

    /// Inserts the given key in the tree, or updates the matching key if 
    /// already present.
    /// 
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

    /// Removes the key matching `k` from the tree and returns it if it exits;
    /// otherwise `None` is returned.
    /// 
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
    /// Returns a new empty BTree.
    /// 
    fn default() -> Self {
        Self::new()
    }
}

/// Creates a new BTree of the order specified by `$order`. If `$order` isn't
/// specified, a tree of default order 16 is created.
/// 
#[macro_export]
macro_rules! btree_order {
    ($order:expr) => {
        BTree::<_, {$order * 2}, {$order * 2 + 1}>::new()
    };
    () => {
        BTree::<_, 32, 33>::new()
    }
}


#[cfg(test)]
mod tests {
    use crate::btree::*;
    
    #[test]
    fn insert() {
        let mut t = btree_order!(3);
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n);
        }
        t.traverse();
        println!("{:#?}", t);
    }
    #[test] 
    fn remove() {
        let mut t = btree_order!(3);
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
        let mut t = btree_order!(3);
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
