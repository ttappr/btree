
//! This crate provides a BTree class that allows its order to be specified
//! on creation. The 'order' is defined as the minimum number of keys a
//! node can hold. A node can possess up to 2 * 'order' keys, and 
//! 2 * 'order' + 1 child nodes. For instance, a tree of order 16 can have from
//! 16 to 32 keys per node, and 17 to 33 children. Only a partially filled
//! root node can have fewer than the order.
//! 
//! During operations, the tree uses tree traversal to locate the relevant
//! node, and binary search on the internal array of the located node. This
//! permits the order to be quite large while not impacting performance.
//! The maximum order that can be selected is 128.

mod btree;
mod if_good;
mod arr;

pub use crate::btree::*;


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
