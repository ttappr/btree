use std::fmt;
use std::mem::{replace, size_of, take};
use std::ops::{Deref, DerefMut, Index, IndexMut};

use array_macro::array;

use crate::splitter::*;

/// A custom array object to hold the keys and children of the BTree.
/// This array object uses the least amount of memory possible. The generic 
/// parameter `S` determines the size of the internal array, WHICH MUST BE
/// NO LARGER THAN 256, as the length of the array is represented as a single 
/// `u8` value.
/// 
pub struct Arr<T, const S: usize> {
    arr: Box<([T; S], u8)>,
}

impl<T, const S: usize> Arr<T, S> 
where 
    T: Default,
{    
    /// Creates a new empty instance of an `Arr`.
    /// 
    pub(crate) fn new() -> Self {
        Self { arr: Box::new((array![_ => T::default(); S], 0)) }
    }

    /// Creates a new `Arr` instance from a single item.
    /// 
    pub(crate) fn from_item(item: T) -> Self {
        let mut arr = Arr::new();
        arr.push(item);
        arr
    }

    /// Creates a new `Arr` instance from a slice of items.
    /// 
    pub(crate) fn from_items(items: &mut [T]) -> Self {
        let mut arr = Arr::new();
        for item in items {
            arr.push(take(item));
        }
        arr
    }

    /// Returns a reference to the item at position `i` if it exists; otherwise,
    /// `None` is returned.
    /// 
    #[allow(dead_code)]
    pub(crate) fn get(&self, i: usize) -> Option<&T> {
        if i < self.len() {
            Some(&self.arr.0[i])
        } else {
            None
        }
    }

    /// Returns a mutable reference to the last item in the array.
    /// 
    pub(crate) fn last_mut(&mut self) -> &mut T {
        &mut self.arr.0[self.len() - 1]
    }

    /// Returns a mutable reference to the first item in the array.
    /// 
    pub(crate) fn first_mut(&mut self) -> &mut T {
        &mut self.arr.0[0]
    }

    /// Returns `true` if the data type of the `Arr` is Zero-Sized. This is 
    /// used by `Node`'s debug print.
    /// 
    pub(crate) fn data_type_is_0_sized(&self) -> bool {
        size_of::<T>() == 0
    }

    /// Returns an object that facilitates splitting an already full `Arr`
    /// instance. The `item` is virtually inserted into the splitter array
    /// at position `i`. It actually floats in another field waiting to be
    /// either popped or inserted in the internal `Arr` when the `Spitter` 
    /// instance is either dropped (or `.into_inner()` is invoked).
    /// 
    pub(crate) fn splitter(&mut self, i: usize, item: T) -> Splitter<'_, T, S>
    {
        Splitter::new(self, i, item)
    }

    /// Gives the number of active elements in the array.
    /// 
    pub(crate) fn len(&self) -> usize {
        self.arr.1 as usize
    }
    
    /// Returns `true` if array is full; `false` otherwise.
    /// 
    pub(crate) fn full(&self) -> bool {
        self.arr.1 == S as u8
    }

    /// Takes the element at the given index, replacing it with the default
    /// value for `T`.
    /// 
    fn take(&mut self, idx: usize) -> T {
        take(&mut self.arr.0[idx])
    }

    /// Replaces the element at `idx` with `replacement` and returns the item
    /// previously at that index.
    /// 
    pub(crate) fn replace(&mut self, idx: usize, replacement: T) -> T {
        replace(&mut self.arr.0[idx], replacement)
    }

    /// Splits the `Arr` in two and returns a new `Arr` containing the elements
    /// taken from the original starting at index `.len() / 2`. The elements
    /// included in the new `Arr` are removed from the original.
    /// 
    #[allow(dead_code)]
    pub(crate) fn split(&mut self) -> Arr<T, S> {
        let mid = self.len() / 2;
        self.split_at(mid)
    }

    /// Splits the `Arr` at `idx` returns a new `Arr` containing the elements
    /// taken from the original starting at index `idx`. The elements
    /// included in the new `Arr` are removed from the original.
    /// 
    pub(crate) fn split_at(&mut self, idx: usize) -> Arr<T, S> {
        let len = self.len() - idx;
        let arr = array![i => if i < len { self.take(idx + i) }
                              else       { T::default()       }; S];
        self.arr.1 = idx as u8;
        Self { arr: Box::new((arr, len as u8)) }
    }

    /// Transfers all elements from `other` into `self` consuming `other`.
    /// 
    pub(crate) fn merge(&mut self, mut other: Arr<T, S>) {
        debug_assert!(other.len() + self.len() <= S, 
                      "Merging both `Arr` objects would result in an array 
                      larger than the limit `S` ({}).", S);
        for (i, j) in (self.len()..S).zip(0..other.len()) {
            self.arr.0[i] = other.take(j);
        }
        self.arr.1 += other.arr.1;
    }

    /// Transfers elements from `other` into `self`, appending them to `self`'s
    /// internal array. 
    /// 
    pub(crate) fn extend(&mut self, other: &mut Self) {
        debug_assert!(other.len() + self.len() <= S, 
                      "Merging both `Arr` objects would result in an array 
                      larger than the limit `S` ({}).", S);
        for (i, j) in (self.len()..S).zip(0..other.len()) {
            self.arr.0[i] = other.take(j);
        }
        self.arr.1 += other.arr.1;
        other.arr.1 = 0;
    }

    /// Appends the given element on to the end of the array.
    /// 
    pub(crate) fn push(&mut self, elm: T) {
        debug_assert!(self.len() < S, 
                      "Attempt to push element onto full `Arr`.");
        self.arr.0[self.len()] = elm;
        self.arr.1 += 1;
    }

    pub(crate) fn push_front(&mut self, elm: T) {
        debug_assert!(self.len() < S, 
                      "Attempt to push element onto full `Arr`.");
        self.insert(0, elm);    
    }

    /// Pops the last item off the internal array, returning it raw (not in an
    /// `Option`).
    /// 
    pub(crate) fn pop(&mut self) -> T {
        if self.arr.1 > 0 {
            self.arr.1 -= 1;
            self.take(self.len())
        } else {
            panic!("Popping from an empty array.");
        }
    }

    /// Pops the first element from the array and returns it raw (not wrapped in
    /// an `Option`).
    /// 
    pub(crate) fn pop_front(&mut self) -> T {
        if self.arr.1 > 0 {
            self.remove(0)
        } else {
            panic!("Popping from an empty array.")
        }
    }

    /// Inserts the given element into the array at the given index. This is
    /// an `O(S)` operation.
    /// 
    pub(crate) fn insert(&mut self, idx: usize, elm: T) {    
        debug_assert!(idx <= self.len(), 
                      "Insertion index ({}) > number of elements in array 
                      ({}).", idx, self.len());
        debug_assert!(!self.full(),    
                      "Attempt to insert into an `Arr` already filled to 
                      capacity ({}).", S);
        for i in (idx..self.len()).rev() {
            self.arr.0[i + 1] = self.take(i)
        }
        self.arr.0[idx] = elm;
        self.arr.1 += 1;
    }

    /// Removes the element at the given index and returns it. Will panic in
    /// debug build if index is beyond current number of elements. This is an
    /// `O(S)` operation.
    ///
    pub(crate) fn remove(&mut self, idx: usize) -> T {
        debug_assert!(idx < self.len(), 
                      "Attempt to remove item at {} from array of length {}.", 
                      idx, self.len());
        let ret = self.take(idx);
        for i in idx..self.len() - 1 {
            self.arr.0[i] = self.take(i + 1);
        }
        self.arr.1 -= 1;
        ret
    }
}

impl<T, const S: usize> Default for Arr<T, S> 
where
    T: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const S: usize> Index<usize> for Arr<T, S> {    
    type Output = T;

    /// Gives `Arr` array indexing features.
    /// 
    fn index(&self, idx: usize) -> &Self::Output {
        debug_assert!(idx < self.len());
        &self.arr.0[idx]
    }
}
impl<T, const S: usize> IndexMut<usize> for Arr<T, S> {
    /// Gives `Arr` mutable array indexing.
    /// 
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        debug_assert!(idx < self.len());
        &mut self.arr.0[idx]
    }
}

/// A custom iterator object for `&Arr` (references).
/// 
pub struct ArrIter<'a, T, const S: usize>(&'a Arr<T, S>, usize);

impl<'a, T, const S: usize> Iterator for ArrIter<'a, T, S> {
    type Item = &'a T;

    /// Returns the next item in `Arr` as a reference.
    /// 
    fn next(&mut self) -> Option<Self::Item> {
        let res = self.0.get(self.1);
        self.1 += 1;
        res
    }
}

impl<'a, T, const S: usize> IntoIterator for &'a Arr<T, S> {
    type Item     = &'a T;
    type IntoIter = ArrIter<'a, T, S>;

    /// Returns an iterator for `&Arr`.
    /// 
    fn into_iter(self) -> Self::IntoIter {
        ArrIter(self, 0)
    }
}

impl<T, const S: usize> Deref for Arr<T, S> {
    type Target = [T];

    /// Allows access to the interfaces provided by the array primitive.
    /// For instance, `.binary_search()`. A slice of the array is returned;
    /// it's size is determined by the number of active items in the array.
    /// 
    fn deref(&self) -> &Self::Target {
        &self.arr.0[0..self.arr.1 as usize]
    }
}

impl<T, const S: usize> DerefMut for Arr<T, S> {

    /// Allows mutable access to the contained array primitive. Returns a
    /// mutable slice of the internal array. Its size is determined by the
    /// internal count of active elements.
    /// 
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.arr.0[0..self.arr.1 as usize]
    }
}

impl<T, const S: usize> fmt::Debug for Arr<T, S> 
where
    T: fmt::Debug,
{
    /// Customizes debug print output making `Arr` appear as a simple array
    /// directly containing the elements of the internal array.
    /// 
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.0[0..self.len()].iter()).finish()
    }
}


#[cfg(test)]
mod tests {
    use crate::arr::*;

    /// Compare two iterable objects, `$a` and `$b`. On failure include
    /// failure message, `$f`, in the test output. `$f` is treated as a
    /// format string and can be followed by 0 or more printable parameters.
    /// ```
    /// //           $a       $b       $f              ...
    /// macro_rules!(&[1, 2], &[1, 2], "Failed at {}", 42);
    /// ```
    ///    
    macro_rules! cmp {
        ($a:expr, $b:expr, $f:literal $(, $g:literal)*) => {
            assert_eq!($a.len(), $b.len(), "{} Lengths were wrong.", 
                       format!($f $(, $g)*));
            $a.iter().zip($b).for_each(|t| assert_eq!(t.0, t.1, $f $(, $g)*));
        }
    }
    
    #[test]
    fn insert() {
        let mut a  = Arr::<_, 10>::new();
        let mut b  = Vec::new();
        let     n1 = [1, 2, 3, 4];
        let     n2 = [5, 6, 7, 8];
        
        // Insert all at 0 and compare.
        for &n in n1.iter() {
            a.insert(0, n);
            b.insert(0, n);
        }
        cmp!(&a, &b, "Insertion at 0 index failed.");
        
        // Insert into `a` interspersing the n1 (rev) and n2 values.
        for (&n, i) in n2.iter().zip((0..).step_by(2)) {
            a.insert(i, n);
            b.insert(i, n);
        }
        cmp!(&a, &b, "Inserting at indices incrementing by 2 failed.");
    }

    #[test]
    fn remove() {
        let mut a = Arr::<_, 10>::new();
        let mut b = (0..10).collect::<Vec<_>>();
        
        // Fill the array with elements from `n` and compare.
        b.iter().for_each(|&n| a.push(n));
        cmp!(&a, &b, "Push operations failed.");
        
        // Remove element at 0 and verify effect.
        assert_eq!(a.remove(0), 0);
        b.remove(0);
        cmp!(&b, &b, "Removing at 0 failed.");
        
        // Remove every other element and verify effect.
        for i in (0..5).step_by(2) {
            let r1 = a.remove(i);
            let r2 = b.remove(i);
            assert_eq!(r1, r2);
        }
        cmp!(&a, &b, "Removing at every other element failed.");
    }
    
    #[test]
    fn split() {
        let mut a = Arr::<_, 10>::new();
        
        // Fill array 0 to 5 twice, split, then verify.
        (0..5).chain(0..5).for_each(|n| a.push(n));
        
        let mut b = a.split();

        cmp!(&a, &b, "Split evenly operation didn't work correctly.");
        
        b = a.split();
        
        cmp!(&a, &[0, 1   ], "Splitting odd number of elements failed case 1.");
        cmp!(&b, &[2, 3, 4], "Splitting odd number of elements failed case 2.");
    }
    
    #[test]
    fn merge() {
        {
            let mut a = Arr::<_, 10>::new();
            let mut b = Arr::<_, 10>::new();
            let     v = (0..5).chain(0..5).collect::<Vec<_>>();
            for n in 0..5 {
                a.push(n);
                b.push(n);
            }
            a.merge(b);
            cmp!(&a, &v, "Failed to merge two equal length arrays.");
        }
        // Try various sizes of arrays while merging.
        for (r1, r2) in [(0..2, 0..5), (0..5, 0..2), 
                         (0..1, 0..8), (0..8, 0..1)]
        {
            let mut a = Arr::<_, 10>::new();
            let mut b = Arr::<_, 10>::new();
            let     v = r1.clone().chain(r2.clone()).collect::<Vec<_>>();
            r1.for_each(|n| a.push(n));
            r2.for_each(|n| b.push(n));
            a.merge(b);
            cmp!(&a, &v, "Failed to merge two unequal length arrays.");
        }
    }
}
