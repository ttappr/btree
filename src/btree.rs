use std::fmt;
use std::mem::take;

use crate::arr::*;
use crate::if_good::*;

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
pub type BTree3<K, V> = BTree<K, V,  6,  7>;
pub type BTree6<K, V> = BTree<K, V, 12, 13>;
pub type BTree9<K, V> = BTree<K, V, 18, 19>;


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
        assert!($order < 128, "`BTree` order must be <= 128.");
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
pub struct BTree<K, V, const M: usize, const N: usize> 
where
    K: Default + Ord,
    V: Default,
{
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
        self.root.insert(key, val).if_some(|(k, v, rt_child)| {
            let lt_child = self.root.take();
            self.root = Branch {
                keys  : Arr::from_item(k),
                vals  : Arr::from_item(v),
                child : Arr::from_items(&mut [lt_child, rt_child]),
            };
        });
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

    /// Returns the fields of either a `Branch` or `Leaf`. Both variants have
    /// keys and vals. An `Option` is returned for the `child` field. This will
    /// have the child array if the node was a `Branch`. A `Seed` node returns
    /// `None`.
    /// 
    fn fields(&self) -> Option<NodeFields<K, V, M, N>>
    {
        match self {
            Branch { keys, vals, child } => {
                Some(NodeFields { keys, vals, child: Some(child) })
            },
            Leaf { keys, vals } => {
                Some(NodeFields { keys, vals, child: None })
            },
            Seed => None,
        }
    }

    /// Returns the fields of either a `Branch` or `Leaf`. Both variants have
    /// keys and vals. An `Option` is returned for the `child` field. This will
    /// have the child array if the node was a `Branch`. A `Seed` node returns
    /// `None`.
    /// 
    #[allow(dead_code)]
    fn fields_mut(&mut self) -> Option<NodeFieldsMut<K, V, M, N>>
    {
        match self {
            Branch { keys, vals, child } => {
                Some(NodeFieldsMut { keys, vals, child: Some(child) })
            },
            Leaf { keys, vals } => {
                Some(NodeFieldsMut { keys, vals, child: None })
            },
            Seed => None,
        }
    }

    /// Inserts the given key and value into the tree, or updates an existing
    /// key's value. If the node this is invoked on was full and had to be split
    /// to accommodate a new entry, the new right child node split off will be 
    /// returned along with the key and value separating the (now) left node and
    /// new right node. The new node will need to be inserted into the caller's
    /// child array, and the key/value will also need to be inserted in the 
    /// caller's respective arrays. If a split didn't occur, this function
    /// returns `None`.
    /// 
    fn insert(&mut self, key: K, val: V) -> Option<(K, V, Self)> {
        let mut retval = None;
        match self {
            Branch { keys, vals, child } => {
                match keys.binary_search(&key) {
                    Ok(i) => { 
                        // Key already exists in current node. Update value.
                        vals[i] = val; 
                    },
                    Err(i) => {
                        // Key doesn't exist in current node Send down to 
                        // child `i`.
                        child[i].insert(key, val).if_some(|(k, v, ch)| {
                            // `child[i]` split. `k` and `v` are the median
                            // key and value between `child[i]` and its new
                            // sibling, `ch`.
                            if keys.full() {
                                let mut k1 = keys.splitter(i, k);
                                let mut v1 = vals.splitter(i, v);
                                let mut c1 = child.splitter(i + 1, ch);

                                let k2 = k1.split_at(M / 2 + 1);
                                let v2 = v1.split_at(M / 2 + 1);
                                let c2 = c1.split_at(M / 2 + 1);
                                let k  = k1.pop();
                                let v  = v1.pop();

                                retval = Some((k, v, Branch {
                                    keys  : k2.into_inner(),
                                    vals  : v2.into_inner(),
                                    child : c2.into_inner(),
                                }));
                            } else {
                                keys.insert(i, k);
                                vals.insert(i, v);
                                child.insert(i + 1, ch);
                            }
                        });
                    },
                }
            },
            Leaf { keys, vals } => {
                match keys.binary_search(&key) {
                    Ok(i) => {
                        vals[i] = val;
                    },
                    Err(i) => {
                        if keys.full() {
                            let mut k1 = keys.splitter(i, key);
                            let mut v1 = vals.splitter(i, val);

                            let k2 = k1.split_at(M / 2 + 1);
                            let v2 = v1.split_at(M / 2 + 1);
                            let k  = k1.pop();
                            let v  = v1.pop();

                            retval = Some((k, v, Leaf {
                                keys  : k2.into_inner(),
                                vals  : v2.into_inner(),
                            }));                            
                        } else {
                            keys.insert(i, key);
                            vals.insert(i, val);
                        }
                    }
                }
            },
            Seed => {
                *self = Leaf { 
                    keys: Arr::from_item(key), 
                    vals: Arr::from_item(val),
                }
            }
        }
        retval
    }

    /// Removes the matching key and its associated value from the tree. The
    /// value is returned; or if the key wasn't present, `None` is returned.
    /// 
    fn remove(&mut self, key: &K) -> Option<V> {
        match self {
            Branch { keys, vals, child } => {
                match keys.binary_search(key) {
                    Ok(i) => {
                        if child[i].n_keys() > M / 2 {
                            let (k, v) = child[i].get_max_descendant();
                            keys[i] = k;
                            Some(vals.replace(i, v))
                        } 
                        else if child[i + 1].n_keys() > M / 2 {
                            let (k, v) = child[i + 1].get_min_descendant();
                            keys[i] = k;
                            Some(vals.replace(i, v))
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
                        let val = child[i].remove(key);
                        if child[i].n_keys() < M / 2 {
                            self.feed(i);
                        }
                        val
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
    
    /// If node child[i] is "hungry" (it's population is below M / 2), it needs 
    /// to be "fed" some keys that it can cannibalize from its siblings, or it 
    /// could be merged with a sibling if neither adjacent sibling has enough 
    /// keys to spare.
    ///
    #[allow(dead_code)]
    fn feed(&mut self, i: usize) {
        match self {
            Branch { keys, vals, child } => {
                let last = child.len() - 1;
                
                if i > 0 && child[i - 1].n_keys() > M / 2 {

                    let (cs1, cs2) = child.split_at_mut(i);
                    cs1[0].borrow_left(&mut cs2[i - 1]);
                } 
                else if i < last && child[i + 1].n_keys() > M / 2 {

                    let (cs1, cs2) = child.split_at_mut(i + 1);
                    cs1[i].borrow_right(&mut cs2[0]);
                }
                else if i < last {
                    let c = child.remove(i + 1);
                    child[i].merge(c);
                }
                else if i > 0 {
                    let c = child.remove(i);
                    child[i - 1].merge(c);
                }
                else if keys.len() + child[0].n_keys() <= M {
                    let mut c = child.pop();
                    c.fields_mut()
                             .map(|NodeFieldsMut { keys: ks, vals: vs, .. }| 
                    {
                        ks.extend(keys);
                        vs.extend(vals);
                    }).unwrap();
                    *self = c;
                }
            }
            _ => panic!("Node::feed() invoked on a Leaf or Seed."),
        }
    }
    
    /// Grabs a key/value and child, if there are any, from `right_sibling` 
    /// and adds them to `self`.
    ///
    fn borrow_right(&mut self, right_sibling: &mut Self) {
        match (self, right_sibling) {
            (Branch { keys: ks1, vals: vs1, child: cs1 },
             Branch { keys: ks2, vals: vs2, child: cs2 }) => {
                let mut c  = cs2.pop_front();
                let (k, v) = c.get_min_descendant();
                ks1.push(k);
                vs1.push(v);
                c.push_back_min_leaf(ks2.pop_front(), vs2.pop_front());
                cs1.push(c);
                // Special case that only happens when called from .merge().
                if cs2.len() == 1 { cs1.push(cs2.pop()); }
            },
            (Leaf { keys: ks1, vals: vs1 },
             Leaf { keys: ks2, vals: vs2 }) => {
                ks1.push(ks2.pop_front());
                vs1.push(vs2.pop_front());
            },
            _ => panic!("Invalid operands for Node::borrow_right()."),
        }        
    }

    /// Grabs a key/value and child, if there are any, from `left_sibling` and
    /// adds them to `self`.
    ///
    fn borrow_left(&mut self, left_sibling: &mut Self) {
        match (self, left_sibling) {
            (Branch { keys: ks1, vals: vs1, child: cs1 },
             Branch { keys: ks2, vals: vs2, child: cs2 }) => {
                let mut c  = cs2.pop();
                let (k, v) = c.get_max_descendant();
                ks1.push_front(k);
                vs1.push_front(v);
                c.push_front_max_leaf(ks2.pop(), vs2.pop());
                cs1.push_front(c);  
            },
            (Leaf { keys: ks1, vals: vs1 },
             Leaf { keys: ks2, vals: vs2 }) => {
                ks1.push_front(ks2.pop());
                vs1.push_front(vs2.pop());
            },
            _ => panic!("Invalid operands for Node::borrow_left()."),
        }
    }

    /// Combines the current node with `other`. The nodes must be of the same
    /// variant.
    /// 
    fn merge(&mut self, other: Self) {
        match (self, other) {
            (    n1 @ Branch { .. }, 
             mut n2 @ Branch { .. }) => {
                while n2.n_keys() > 0 {
                    n1.borrow_right(&mut n2);
                }
             },
             (Leaf { keys: ks1, vals: vs1 }, 
              Leaf { keys: ks2, vals: vs2 }) => {
                ks1.merge(ks2);
                vs1.merge(vs2);
             },
            _ => panic!("Invalid operands for Node::merge()."),
        }
    }

    /// Descends the tree from the current node to find it's maximum key.
    /// This key and its value are removed from their hosting node and returned.
    /// 
    fn get_max_descendant(&mut self) -> (K, V) {
        let mut curr    = self; 
        let mut key_val = None;
        loop {
            match curr {
                Branch { child, .. } => {
                    curr = child.last_mut();
                },
                Leaf { keys, vals } => { 
                    key_val = Some((keys.pop(), vals.pop()));
                    break; 
                },
                Seed => break,
            }
        }
        key_val.unwrap()
    }

    /// Descends the tree from the current node to find that branch's minimum
    /// key and its associated value. The key and value are removed from the 
    /// tree and returned.
    /// 
    fn get_min_descendant(&mut self) -> (K, V) {
        let mut curr    = self;
        let mut key_val = None;
        loop {
            match curr {
                Branch { child, .. } => {
                    curr = child.first_mut();
                },
                Leaf { keys, vals } => { 
                    key_val = Some((keys.pop_front(), 
                                    vals.pop_front()));
                    break; 
                },
                Seed => break,
            }
        }
        key_val.unwrap()
    }

    /// Locates the minimum descendant leaf of the node and pushes `key` and
    /// `val` on the fronts of the respective array fields.
    /// 
    fn push_front_max_leaf(&mut self, key: K, val: V) {
        let mut curr = self;
        loop {
            match curr {
                Branch { child, .. } => {
                    curr = child.last_mut();
                },
                Leaf { keys, vals } => {
                    keys.push_front(key);
                    vals.push_front(val);
                    break;
                },
                Seed => break,
            }
        }
    }

    /// Locates the maximum descendant leaf and pushes `key` and `val` on the
    /// front of their respective array fields.
    /// 
    fn push_back_min_leaf(&mut self, key: K, val: V) {
        let mut curr = self;
        loop {
            match curr {
                Branch { child, .. } => {
                    curr = child.first_mut();
                },
                Leaf { keys, vals } => {
                    keys.push(key);
                    vals.push(val);
                    break;
                }
                Seed => break,
            }
        }
    }
}
impl<K, V, const M: usize, const N: usize> Default for Node<K, V, M, N> {

    /// Returns the default value for `Node`, which is the variant `Seed`.
    /// 
    fn default() -> Self {
        Seed
    }
}

impl<K, V, const M: usize, const N: usize> fmt::Debug for Node<K, V, M, N> 
where
    K: fmt::Debug + Default + Ord,
    V: fmt::Debug + Default,
{
    /// Customizes debug print output making `Node` appear as a simple list
    /// of key/value pairs and holding a field of children.
    /// 
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let variant = match self {
            Seed          => "Seed",
            Branch { .. } => "Branch",
            Leaf   { .. } => "Leaf",
        };
        let mut builder = f.debug_struct(variant);

        self.fields().if_some(|NodeFields { keys, vals, child }| {
        
            if vals.data_type_is_0_sized() {
                builder.field("keys", 
                              &keys.into_iter()
                                   .collect::<Vec<_>>());
            } else {
                builder.field("pairs", 
                              &keys.into_iter().zip(vals)
                                   .collect::<Vec<_>>());
            }
            child.if_some(|child| { builder.field("child", child); });
        });
        builder.finish()
    }
}

/// Internal struct returned by convenience methods to access fields of the 
/// variants of `Node`.
/// 
struct NodeFields<'a, K, V, const M: usize, const N: usize> {
    keys  : &'a Arr<K, M>,
    vals  : &'a Arr<V, M>,
    child : Option<&'a Arr<Node<K, V, M, N>, N>>,
}

/// Internal struct returned by convenience methods to access fields of the 
/// variants of `Node`. Mutable version.
/// 
#[allow(dead_code)]
struct NodeFieldsMut<'a, K, V, const M: usize, const N: usize> {
    keys  : &'a mut Arr<K, M>,
    vals  : &'a mut Arr<V, M>,
    child : Option<&'a mut Arr<Node<K, V, M, N>, N>>,
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;
    use crate::btree::*;

    trait TreeIFace<K, V> { 
        fn insert (&mut self, key:  K, val: V); 
        fn get    (    &self, key: &K)  -> &V; 
    }
    impl<K, V, const M: usize, const N: usize> 
        TreeIFace<K, V> for BTree<K, V, M, N> 
    where 
        K: Default + Ord,
        V: Default,
    {
        fn insert (&mut self, key:  K, val: V) { self.insert(key, val); }
        fn get    (    &self, key: &K ) -> &V  { self.get(key).unwrap() }
    }

    #[test]
    fn insert() {
        let mut t = BTree3::new();
        for n in [10, 20, 5, 6, 12, 30, 7, 17] {
            t.insert(n, ());
        }
        println!("{:#?}", t);
    }

    #[test] 
    fn remove() {
        let mut t = BTree3::new();
        let     a = [10, 20, 5, 6, 12, 30, 7, 17];
        let     b = [10, 7, 12, 17, 5];

        for n in a {
            t.insert(n, ());
        }
        println!("Full tree: {:#?}", t);
        for n in b {
            println!("Removing {}...", n);
            t.remove(&n);
            println!("{:#?}", t);
        }
    }
    
    #[test]
    fn get() {
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
        let mut bt6  = BTree6::new();    // Order 6 BTree.
        let mut bt8  = btree_order!(8);  // Order 8 - arbitrary order via macro.

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
            assert_eq!(bt8.get(&n), None);        }        
    }

    #[test]
    fn many_insertions() {
        let mut k = (0..1000).collect::<Vec<_>>();
        let     v = (0..1000).collect::<Vec<_>>();

        for bt in [&mut BTree3::new() as &mut dyn TreeIFace<_, _>,
                   &mut BTree6::new(),
                   &mut BTree9::new(),]
        {
            k.shuffle(&mut rand::thread_rng());
            let it = k.iter().copied().zip(v.iter().copied());
            
            for (k, v) in it.clone() {
                bt.insert(k, v);
            }            
            for (k, v) in it {
                assert_eq!(bt.get(&k), &v);
            }
        }
    }

    #[test]
    fn overwriting_values() {
        let mut bt  = BTree3::new();
        let mut rng = rand::thread_rng();
        let mut k   = (0..1000).collect::<Vec<_>>();
        let     v   = (0..1000).collect::<Vec<_>>();

        k.shuffle(&mut rng);
        let mut it = k.iter().copied().zip(v.iter().copied());
        
        for (k, v) in it.clone() {
            bt.insert(k, v);
        }
        for (k, v) in it {
            assert_eq!(bt.get(&k), Some(&v));
        }

        k.shuffle(&mut rng);
        it = k.iter().copied().zip(v.iter().copied());

        for (k, v) in it.clone() {
            bt.insert(k, v);
        }
        for (k, v) in it {
            assert_eq!(bt.get(&k), Some(&v));
        }
    }

    #[test]
    fn seed() {
        assert_eq!(format!("{:#?}", Node::<&str, (), 6, 7>::Seed), "Seed");
    }
}
