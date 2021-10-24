# btree crate

Work in progress.

An experimental BTree implemented in Rust. Insertion and search work well, and
removal works for the most part but needs some finishing touches to ensure
the tree remains properly balanced during the operation.

An interesting feature of this implementation is it allows developers to specify
the order of the tree on creation. This implementation defines *order* as the 
minimum number of keys any non-root node may have. A tree of order 16 can have 
as few as 16 keys and a maximum of 32 keys and 33 child nodes.

Because the tree uses a combination of tree traversal and binary search to
locate its nodes and keys, the order can be considerably large without 
sacrificing performance. Traversal is used to locate the nodes while binary 
search is performed on the internal arrays of the nodes to locate key positions. 
Insertions and deletions will however degrade performance slightly as 
the order increases, but this *may* be negligible due to data locality and 
caching; some experimentation and benchmarking will be done after the tree
is fully implemented.


## Example Code

```rust
    let mut bt = btree_order!(3);

    let kv = [(10, 'j'), (20, 't'), (5, 'e'), (6,  'f'), 
              (12, 'l'), (30, '~'), (7, 'g'), (17, 'q')];

    for (k, v) in kv {
        bt.insert(k, v);
    }
    for (k, v) in kv {
        assert_eq!(bt.get(&k), Some(&v));
    }
    for n in [18, 2, 9, 42, 100] {
        assert_eq!(bt.get(&n), None);
    }
```
