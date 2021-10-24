use std::fmt::Debug;
use std::mem::{replace, take};

use crate::arr::*;

use Node::*;


/// Aliases to help the compiler with type inference when declaring instances of
/// the tree.
/// ```
/// use btree::BTree6;
/// 
/// let mut bt = BTree6::new(); // Order 6 tree.
/// bt.insert("foo", "bar");
/// ```
/// 
pub type BTree3<K, V> = BTree<K, V, 6, 7>;
pub type BTree6<K, V> = BTree<K, V, 12, 13>;


/// Creates a new `BTree` of the order specified by `$order`. If `$order` isn't
/// specified, a tree of default order 16 is created.
/// ```
/// use btree::*;
/// 
/// let mut bt = btree_order!(3);
/// let     d  = [(3, 'c'), (7, 'g'), (24, 'x')];
/// 
/// for (k, v) in d {
///     bt.insert(k, v);
/// }
/// for (k, v) in d {
///     assert_eq!(bt.get(&k), Some(&v));
/// }
/// ```
/// 
#[macro_export]
macro_rules! btree_order {
    ($order:expr) => {{
        assert!($order <= 128, "`BTree` order must be <= 128.");
        BTree::<_, _, {$order * 2}, {$order * 2 + 1}>::new()
    }}
}

/// The main class for the tree. Holds the root node. The *order* of the tree is
/// defined as the minimum number of keys that can populate a node. The maximum
/// number of keys (`M`) must be `order * 2`, and the maximum number of children
/// (`N`) must be `order * 2 + 1`.
/// 
/// The *order* of the tree can be considerably large (up to 128) as the 
/// operations on the internal array of the node use binary search to locate
/// keys.
/// 
/// # Generic Parameters
/// * `K`   - The key type.
/// * `V`   - The value type.
/// * `M`   - The maximum number of keys of a node (must be `order * 2`).
/// * `N`   - The maximum number of children of any node 
///           (must be `order * 2 + 1`).
/// 
#[derive(Debug)]
pub struct BTree<K, V, const M: usize, const N: usize> {
    root  : Node<K, V, M, N>,
}

impl<K, V, const M: usize, const N: usize> BTree<K, V, M, N> 
where
    K: Default + Ord,
    V: Default,
{
    /// Returns a new `BTree` with a `Seed` as root.
    /// 
    pub fn new() -> Self {
        Self { root: Seed }
    }

    /// Returns a reference to the value associated with the given key. If the
    /// key wasn't present in the tree, `None` is returned instead;
    /// 
    pub fn get(&self, key: &K) -> Option<&V> {
        self.root.get(key)
    }

    /// Inserts the given key and value in the tree, or updates the associated 
    /// value if the key was already present.
    /// 
    pub fn insert(&mut self, key: K, val: V) {
        // TODO - If the key is already present, should we split the node 
        //        anyway to avoid the wasted work of probing for the key?
        if self.root.full() {
            let mut ch1   = self.root.take();
            let mut ch2   = ch1.split();
            let mut keys  = Arr::new();
            let mut vals  = Arr::new();
            let mut child = Arr::new();
            let (k, v)    = ch1.pop();
            
            if key < k { ch1.insert(key, val); } 
            else       { ch2.insert(key, val); }
            
            keys.push(k);
            vals.push(v);
            child.push(ch1);
            child.push(ch2);
            
            self.root = Branch { keys, vals, child };
        } else {
            self.root.insert(key, val);
        }
    }

    /// Removes the matching key from the tree and returns its associated
    /// value. If the key wasn't present, `None` is returned.
    /// 
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let val = self.root.remove(key);
        if self.root.n_keys() == 0 {
            self.root = Seed;
        }
        val
    }    
}

impl<K, V, const M: usize, const N: usize> Default for BTree<K, V, M, N> 
where
    K: Default + Ord,
    V: Default,    
{
    /// Returns a new empty BTree.
    /// 
    fn default() -> Self {
        Self::new()
    }
}


/// The node type of the tree. The bulk of the tree's functionality is coded
/// within this class.
/// 
/// # Variants
/// * `Seed`    - Represents an empty node.
/// * `Branch`  - A non-terminal node.
/// * `Leaf`    - A terminal node.
/// 
/// # Generic Parameters
/// * `K`   - The key type.
/// * `V`   - The value type.
/// * `M`   - The maximum number of keys (must be `order * 2`).
/// * `N`   - The maximum number of children (must be `order * 2 + 1`).
/// 
#[derive(Debug)]
pub enum Node<K, V, const M: usize, const N: usize> {
    Seed,
    Branch{ keys: Arr<K, M>, vals: Arr<V, M>, child: Arr<Node<K, V, M, N>, N> },
    Leaf  { keys: Arr<K, M>, vals: Arr<V, M>                                  },
}

impl<K, V, const M: usize, const N: usize> Node<K, V, M, N> 
where
    K: Default + Ord,
    V: Default,
{
    /// Returns the number of keys in the node.
    /// 
    fn n_keys(&self) -> usize {
        match self {
            Branch { keys, .. } => keys.len(),
            Leaf   { keys, .. } => keys.len(),
            Seed                => 0,
        }
    }

    /// Pops the last key and value from the current node. Panics if the
    /// node is empty.
    /// 
    fn pop(&mut self) -> (K, V) {
        match self {
            Branch { keys, vals, .. } => (keys.raw_pop(), vals.raw_pop()),
            Leaf   { keys, vals     } => (keys.raw_pop(), vals.raw_pop()),
            Seed                      => panic!("Popping from a `Seed`."),
        }
    }

    /// Reports whether the node has reached the maximum key population.
    /// 
    fn full(&self) -> bool {
        match self {
            Branch { keys, .. } => keys.full(),
            Leaf   { keys, .. } => keys.full(),
            Seed                => false,
        }
    }

    /// Returns the node, replacing `self` with the `Seed` variant.
    /// 
    fn take(&mut self) -> Self {
        take(self)
    }

    /// Returns a reference to the value associated with the given key. If the
    /// key isn't present in the tree, `None` is returned instead.
    /// 
    fn get(&self, key: &K) -> Option<&V> {
        match self {
            Branch { keys, vals, child } => {
                keys.binary_search(key)
                    .map_or_else(|i| child[i].get(key),
                                 |i| Some(&vals[i]))
            },
            Leaf { keys, vals } => {
                keys.binary_search(key).map(|i| &vals[i]).ok()
            },
            Seed => None,
        }
    }

    /// Inserts the given key into the tree, or updates the existing matching
    /// key.
    /// 
    fn insert(&mut self, k: K, v: V) {
        match self {
            Branch { keys, vals, child } => {
                match keys.binary_search(&k) {
                    Err(i) => {
                        if child[i].full() {
                            let (k, v) = child[i].pop();
                            let ch     = child[i].split();

                            child.insert(i + 1, ch);
                            keys.insert(i, k);
                            vals.insert(i, v);
                        }
                        child[i].insert(k, v);
                    }, 
                    Ok(i) => { keys[i] = k; }
                }
            },
            Leaf { keys, vals } => {
                match keys.binary_search(&k) {
                    Err(i) => { keys.insert(i, k); vals.insert(i, v); },
                    Ok(i)  => { keys[i] = k;       vals[i] = v;       },
                }
            },
            Seed => { 
                let mut keys = Arr::new();
                let mut vals = Arr::new();
                keys.push(k);
                vals.push(v);
                *self = Leaf { keys, vals };
            },
        }
    }

    /// Splits a node in half, returning a new node containing the larger keys.
    /// 
    fn split(&mut self) -> Node<K, V, M, N> {
        match self {
            Branch { keys, vals, child } => {
                let k2 = keys.split();
                let v2 = vals.split();
                let c2 = child.split();
                Branch { keys: k2, vals: v2, child: c2 }
            },
            Leaf { keys, vals } => {
                let k2 = keys.split();
                let v2 = vals.split();
                Leaf { keys: k2, vals: v2 }
            },
            Seed => panic!("Can't split a Seed."),
        }
    }

    /// Removes the matching key and its associated value from the tree. The
    /// value is returned; or if the key wasn't present, `None` is returned.
    /// 
    fn remove(&mut self, key: &K) -> Option<V> {
        match self {
            Branch { keys, vals, child } => {
                match keys.binary_search(key) {
                    Ok(i) => {
                        if child[i].n_keys() >= M / 2 {
                            let (k, v) = child[i].max_descendant();
                            keys[i] = k;
                            Some(replace(&mut vals[i], v))
                        } 
                        else if child[i + 1].n_keys() >= M / 2 {
                            let (k, v) = child[i + 1].min_descendant();
                            keys[i] = k;
                            Some(replace(&mut vals[i], v))
                        } 
                        else {
                            let c = child.remove(i + 1);
                            let _ = keys.remove(i);
                            let v = vals.remove(i);
                            child[i].merge(c);
                            if keys.len() == 0 {
                                *self = child.remove(i);
                            }
                            Some(v)
                        }
                    },
                    Err(i) => {
                        child[i].remove(key)
                    },
                }
            },
            Leaf { keys, vals } => {
                keys.binary_search(key).map(|i| { 
                    keys.remove(i); 
                    vals.remove(i) 
                }).ok()
            },
            Seed => None,
        }
    }

    /// Combines the current node with `other`. The nodes must be of the same
    /// variant.
    /// 
    fn merge(&mut self, other: Node<K, V, M, N>) {
        match (self, other) {
            (Branch { keys: k1, vals: v1, child: c1 }, 
             Branch { keys: k2, vals: v2, child: c2 }) => {
                k1.merge(k2);
                v1.merge(v2);
                c1.merge(c2);
             },
             (Leaf { keys: k1, vals: v1 }, 
              Leaf { keys: k2, vals: v2 }) => {
                k1.merge(k2);
                v1.merge(v2);
             },
            _ => panic!("Invalid operands for Node::merge()."),
        }
    }

    /// Descends the tree from the current node to find it's maximum key.
    /// This key and its value are removed from their hosting node and returned.
    /// 
    fn max_descendant(&mut self) -> (K, V) {
        let mut curr    = self; 
        let mut key_val = None;
        loop {
            match curr {
                Branch { keys: _, vals: _, child } => {
                    curr = child.last_mut().unwrap();
                },
                Leaf { keys, vals } => { 
                    key_val = Some((keys.raw_pop(), vals.raw_pop()));
                    break; 
                },
                Seed => { break; }
            }
        }
        key_val.unwrap()
    }


    /// Descends the tree from the current node to find that branch's minimum
    /// key and its associated value. The key and value are removed from the 
    /// tree and returned.
    /// 
    fn min_descendant(&mut self) -> (K, V) {
        let mut curr    = self;
        let mut key_val = None;
        loop {
            match curr {
                Branch { keys: _, vals: _, child } => {
                    curr = &mut child[0];
                },
                Leaf { keys, vals } => { 
                    key_val = Some((keys.raw_pop_front(), 
                                    vals.raw_pop_front()));
                    break; 
                },
                Seed => { break; }
            }
        }
        key_val.unwrap()
    }
}
impl<K, V, const M: usize, const N: usize> Default for Node<K, V, M, N> {

    /// Returns the default value for `Node`, which is the variant `Seed`.
    /// 
    fn default() -> Self {
        Seed
    }
}


#[cfg(test)]
mod tests {
    use crate::btree::*;
    
    #[test]
    fn insert() {
        let mut t = BTree3::new();
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n, n);
        }
        println!("{:#?}", t);
    }
    #[test] 
    fn remove() {
        let mut t = BTree3::new();
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n, n);
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
        let mut t = BTree3::new();
        
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n, n);
        }
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            assert_eq!(t.get(&n), Some(&n));
        }
        for n in [18, 2, 9, 42, 100] {
            assert_eq!(t.get(&n), None);
        }
    }

    #[test]
    fn example() {
        let mut bt6 = BTree6::new();    // Order 6 BTree.
        let mut bt8 = btree_order!(8);  // Order 8 - arbitrary order via macro.

        let kv = [(10, 'j'), (20, 't'), (5, 'e'), (6,  'f'), 
                  (12, 'l'), (30, '~'), (7, 'g'), (17, 'q')];
    
        for (k, v) in kv {
            bt6.insert(k, v);
            bt8.insert(k, v);
        }
        for (k, v) in kv {
            assert_eq!(bt6.get(&k), Some(&v));
            assert_eq!(bt8.get(&k), Some(&v));
        }
        for n in [18, 2, 9, 42, 100] {
            assert_eq!(bt6.get(&n), None);
            assert_eq!(bt8.get(&n), None);
        }        
    }
}
