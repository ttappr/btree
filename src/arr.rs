use std::fmt;
use std::mem::take;
use std::ops::{Deref, DerefMut, Index, IndexMut};

use array_macro::array;

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

    /// Returns the element at the given index if one is present, or `None`
    /// if the index is larger than the number of elements as given by 
    /// `.len()`.
    /// 
    pub(crate) fn get(&self, idx: usize) -> Option<&T> {
        if idx < self.len() { Some(&self.arr.0[idx]) } 
        else                { None                   }
    }

    /// Returns `Some(&mut T)` if the index is valid; `None` otherwise.
    /// 
    #[allow(unused)]
    pub(crate) fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx < self.len() { Some(&mut self.arr.0[idx]) } 
        else                { None                       }
    }

    /// Takes the element at the given index, replacing it with the default
    /// value for `T`.
    /// 
    fn take(&mut self, idx: usize) -> T {
        take(&mut self.arr.0[idx])
    }

    /// Splits the `Arr` in two and returns a new `Arr` containing the elements
    /// taken from the original starting at index `.len() / 2`. The elements
    /// included in the new `Arr` are removed from the original.
    /// 
    pub(crate) fn split(&mut self) -> Arr<T, S> {
        let mid = self.len() / 2;
        let len = self.len() - mid;
        let arr = array![i => if i < len { self.take(mid + i) } 
                              else       { T::default()       }; S];
        self.arr.1 = mid as u8;
        Self { arr: Box::new((arr, len as u8)) }
    }

    /// Transfers all elements from `other` into `self` consuming `other`.
    /// 
    pub(crate) fn merge(&mut self, mut other: Arr<T, S>) {
        assert!(other.len() + self.len() <= S, 
                "Merging both `Arr` objects would result in an array larger 
                than the limit `S` ({}).",
                S);
        for (i, j) in (self.len()..S).zip(0..other.len()) {
            self.arr.0[i] = other.take(j);
        }
        self.arr.1 += other.arr.1;
    }

    /// Appends the given element on to the end of the array.
    /// 
    pub(crate) fn push(&mut self, elm: T) {
        assert!(self.len() < S, "Attempt to push element onto full `Arr`.");
        self.arr.0[self.len()] = elm;
        self.arr.1 += 1;
    }

    /// Removes and returns the last element in the array as `Some(T). If the 
    /// array was empty `None` is returned.
    /// 
    pub(crate) fn pop(&mut self) -> Option<T> {
        if self.arr.1 > 0 {
            self.arr.1 -= 1;
            Some(self.take(self.len()))
        } else {
            None
        }
    }

    pub(crate) fn raw_pop(&mut self) -> T {
        if self.arr.1 > 0 {
            self.arr.1 -= 1;
            self.take(self.len())
        } else {
            panic!("Popping from an empty array.");
        }
    }

    /// Removes and returns the first element in the array if there are elements
    /// in the array; `None` otherwise.
    /// 
    #[allow(unused)]
    pub(crate) fn pop_front(&mut self) -> Option<T> {
        if self.arr.1 > 0 {
            Some(self.remove(0))
        } else {
            None
        }
    }

    pub(crate) fn raw_pop_front(&mut self) -> T {
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
        assert!(idx <= self.len(), 
                "Insertion index ({}) > number of elements in array ({}).", 
                idx, self.len());
        assert!(!self.full(),    
                "Attempt to insert into an `Arr` already filled to capacity 
                ({}).", S);
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
        assert!(idx < self.len(), 
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
impl<T, const S: usize> Index<usize> for Arr<T, S> 
where
    T: Default,
{    
    type Output = T;

    /// Gives `Arr` array indexing features.
    /// 
    fn index(&self, idx: usize) -> &Self::Output {
        assert!(idx < self.len());
        &self.arr.0[idx]
    }
}
impl<T, const S: usize> IndexMut<usize> for Arr<T, S> 
where
    T: Default,
{
    /// Gives `Arr` mutable array indexing.
    /// 
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        assert!(idx < self.len());
        &mut self.arr.0[idx]
    }
}

/// A custom iterator object for `&Arr` (references).
/// 
pub struct ArrIter<'a, T, const S: usize>(&'a Arr<T, S>, usize);

impl<'a, T, const S: usize> Iterator for ArrIter<'a, T, S> 
where
    T: Default,
{
    type Item = &'a T;

    /// Returns the next item in `Arr` as a reference.
    /// 
    fn next(&mut self) -> Option<Self::Item> {
        let res = self.0.get(self.1);
        self.1 += 1;
        res
    }
}

impl<'a, T, const S: usize> IntoIterator for &'a Arr<T, S> 
where
    T: Default,
{
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
