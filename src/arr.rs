#![allow(unused)]

use std::mem::take;
use std::ops::{Deref, DerefMut, Index, IndexMut};

use array_macro::array;

/// A featured array object that uses the least memory possible. The generic 
/// parameter `S` determines the size of the internal array, which should be
/// no larger than 256. The number of elements in the array is represented by
/// a single `u8` value. The overhead for this array type is only 9 bytes
/// (Box pointer + size byte); the overhead for `Vec` would be 24 bytes,
/// which includes a pointer to an array (8 bytes), the size (8 bytes), and
/// reference to an allocator (8 bytes).
/// 
pub(crate) struct Arr<T, const S: usize> {
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

    /// Returns `Some(&T)` containing the item at the given index, or `None`
    /// if the index is larger than the number of elements.
    /// 
    pub(crate) fn get(&self, idx: usize) -> Option<&T> {
        if idx < self.len() { Some(&self.arr.0[idx]) } 
        else                { None                   }
    }

    /// Returns `Some(&mut T)` if the index is valid; `None` otherwise.
    /// 
    pub(crate) fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx < self.len() { Some(&mut self.arr.0[idx]) } 
        else                { None                       }
    }

    /// Takes the element at the given index, replacing it with the default
    /// value for `T`.
    /// 
    pub(crate) fn take(&mut self, idx: usize) -> T {
        take(&mut self.arr.0[idx])
    }

    /// Splits the `Arr` into two and returns an `Arr` containing the elements
    /// from the original starting at index `S / 2`. The elements included in 
    /// the split `Arr` are removed from the original `Arr`.
    /// 
    pub(crate) fn split(&mut self) -> Arr<T, S> {
        let mid = S / 2;
        let len = if self.len() > mid { self.len() - mid } else { 0 };
        let arr = array![i => if i < mid { self.take(mid + i) } 
                              else       { T::default()       };
                         S];
        self.arr.1 = self.arr.1.min(mid as u8);
        Self { arr: Box::new((arr, len as u8)) }
    }

    /// Merges elements from `other` into `self`.
    /// 
    pub(crate) fn merge(&mut self, mut other: Arr<T, S>) {
        assert!(other.len() + self.len() <= S);
        for (i, j) in (self.len()..S).zip(0..other.len()) {
            self.arr.0[i] = other.take(j);
        }
        self.arr.1 += other.arr.1;
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

/// A custom iterator object for `&Arr`.
/// 
pub(crate) struct ArrIter<'a, T, const S: usize>(&'a Arr<T, S>, usize);

impl<'a, T, const S: usize> Iterator for ArrIter<'a, T, S> 
where
    T: Default,
{
    type Item = &'a T;

    /// Returns the next item in `Arr`.
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

    // TODO - Review this implementation and determine if it will be affected
    //        by the v2021 change coming that affects the way primitive arrays 
    //        currently implement of this trait.
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