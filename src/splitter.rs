use std::mem::take;
use std::ops::{Deref, DerefMut};

use crate::arr::*;

use RefOrConcrete::*;

/// A convenience class that helps split `Arr` arrays. A single new element
/// can be added to a wrapped `Arr` instance which is already filled to 
/// capacity. The splitter object will act as if the element had ben added
/// and permit splitting the array and popping values from it. 
/// 
/// The inner `Arr` can be extracted via the `.into_inner()` if it's in the 
/// `ArrSplitter` instance that was returned by the `.split_at()` method.
/// Invoking `.into_inner()` will cause the floating new item to be inserted
/// into the inner `Arr` if it hasn't already been popped. For the original
/// splitter holding the `Arr` reference prior to the split, the floating
/// element will be inserted if it's still there when the splitter goes out
/// of scope and is dropped, or when `.resolve()` is called.
/// 
/// The application of this class is very specific. The expectation is an
/// `Arr` instance is added along with a floating element and its position on
/// creation, the array will be split, then the original splitter will have
/// its last element popped.  
/// 
#[derive(Debug)]
pub(crate) struct ArrSplitter<'a, T, const S: usize> 
where
    T: Default,
{
    arr: RefOrConcrete<'a, T, S>, 
    pos: usize, 
    elm: Option<T>,
}

impl<'a, T, const S: usize> ArrSplitter<'a, T, S> 
where 
    T: Default,
{
    /// Creates a new `ArrSplitter` instance with a floating element, `elm` at
    /// position `i`.
    /// 
    pub(crate) fn new(arr: &'a mut Arr<T, S>, pos: usize, elm: T) -> Self {
        ArrSplitter { arr: Ref(arr), pos, elm: Some(elm) }
    }

    /// Splits the object at `i` as if the floating element were already
    /// inserted into the internal array. A new instance of a splitter is
    /// returned holding the rightmost values. Internally it will hold a 
    /// concrete instance of `Arr` that can be obtained with `.into_inner()`.
    /// 
    pub(crate) fn split_at(&mut self, i: usize) -> Self {
        if i < self.pos {
            ArrSplitter {
                arr: Conc(Arr::split_at(&mut self.arr, i)), 
                pos: self.pos - i, 
                elm: self.elm.take() 
            }
        } else if i > self.pos + 1 {
            ArrSplitter {
                arr: Conc(Arr::split_at(&mut self.arr, i - 1)),
                pos: 0,
                elm: None,
            }
        } else if i == self.pos {
            ArrSplitter {
                arr: Conc(Arr::split_at(&mut self.arr, i)),
                pos: 0,
                elm: self.elm.take(),
            }
        } else /* if i == self.pos + 1 */ {
            ArrSplitter {
                arr: Conc(Arr::split_at(&mut self.arr, i - 1)),
                pos: 0,
                elm: None,
            }
        }
    }

    /// Pops items off the end of the splitter's virtual array as if the 
    /// floating element were part of the internal array.
    /// 
    pub(crate) fn pop(&mut self) -> T {
        if self.elm.is_some() && self.pos == self.arr.len() {
            self.elm.take().unwrap()
        } else {
            self.arr.raw_pop()
        }
    }

    /// Consumes the splitter returning the inner `Arr` instance. This can only
    /// be invoked on the splitter returned by the `.split_at()` method. The
    /// floating element will be inserted into the `Arr` if it's still there.
    ///
    pub(crate) fn into_inner(mut self) -> Arr<T, S> {
        self.consolidate();
        match take(&mut self.arr) {
            Conc(a) => a,
            _ => panic!("Can only call .into_inner() on Splitter holding a
                         concrete instance of Arr."),
        }
    }

    /// Causes the internal floating element to be inserted into the internal
    /// `Arr` instance. This should not be called prior to splitting the 
    /// original `ArrSplitter` as the internal `Arr` will be full and an 
    /// insertion attempt will cause a panic.
    /// 
    pub(crate) fn consolidate(&mut self) {
        if self.elm.is_some() {
            self.arr.insert(self.pos, self.elm.take().unwrap());
        }
    }
}

impl<'a, T, const S: usize> Drop for ArrSplitter<'a, T, S> 
where
    T: Default,
{
    /// Called when a splitter instance is dropped. It will ensure the internal
    /// floating element is inserted into the wrapped `Arr`.
    /// 
    fn drop(&mut self) {
        match &self.arr {
            Conc(_) => self.consolidate(),
            Ref(_) => self.consolidate(),
            _ => { },
        }
    }
}

/// An enum that wraps either a reference to an `Arr`, or a concrete instance.
/// 
#[derive(Debug)]
pub(crate) enum RefOrConcrete<'a, T, const S: usize> {
    Void,
    Ref(&'a mut Arr<T, S>),
    Conc(Arr<T, S>),
}
impl<'a, T, const S: usize> Default for RefOrConcrete<'a, T, S> {
    /// Provides the default value for the `RefOrConcrete` enum. Returns
    /// the `Void` variant.
    /// 
    fn default() -> Self {
        Void
    }
}
impl<'a, T, const S: usize> Deref for RefOrConcrete<'a, T, S> {
    type Target = Arr<T, S>;

    /// Makes the internal array transparently accessible.
    /// 
    fn deref(&self) -> &Self::Target {
        match self {
            Ref(r) => r,
            Conc(c) => c,
            Void => panic!("Void - no contained reference or object."),
        }
    }
}
impl<'a, T, const S: usize> DerefMut for RefOrConcrete<'a, T, S> {

    /// Makes the internal array transparently accessible and mutable.
    /// 
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Ref(r) => r,
            Conc(c) => c,
            Void => panic!("Void - no contained reference or object."),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::splitter::*;
    
    #[test]
    fn pop() {
        let mut v  = (0..10).collect::<Vec<_>>();
        let mut a  = Arr::<_, 10>::from_items(&mut v);
        let mut s1 = ArrSplitter::new(&mut a, 4, 42);
        let mut s2 = s1.split_at(6);

        s1.consolidate();
        s2.consolidate();

        //println!("{}", s1.pop());
        println!("{:?}", s1);
        println!("{:?}", s2);
    }
}