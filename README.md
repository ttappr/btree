# btree crate

Work in progress.

An experimental BTree implemented in Rust. Insertion and search work well, and
key removal works for the most part but needs some finishing touches to ensure
the tree remains properly balanced during the operation.

An interesting feature of this implementation is it allows the user to specify
the order of the tree on creation. The *order* is defined as the minimum
number of keys any non-root node may have. A tree of order 16 can have as few
as 16 keys and a maximum of 32 keys and 33 child nodes.

Because the tree uses a combination of tree traversal and binary search to
locate its nodes and keys, the order can be considerably high without 
sacrificing the performance of searches. Traversal is used to locate the nodes 
while binary search is performed on the internal arrays of the nodes to locate 
key positions. Insertions and deletions will however degrade very slightly as
the order increases - the internal array is simply that: an array.

So the tree's order can be fine tuned to find the sweet spot for performance.
Applications that infrequently mutate the tree can benefit from larger orders, 
while for the opposite case, smaller orders can be set.

## Example Code

```rust
    let mut bt = btree_order!(128);
    
    for n in [10, 20, 5, 6, 12, 30, 7, 17] {
        bt.insert(n);
    }
    for n in [10, 20, 5, 6, 12, 30, 7, 17] {
        assert_eq!(bt.search(&n), Some(&n));
    }
    for n in [18, 2, 9, 42, 100] {
        assert_eq!(bt.search(&n), None);
    }
```
