use std::mem::take;
use std::ops::{Deref, DerefMut};

use crate::arr::*;

use RefOrConcrete::*;

/// Objects of this class are returned by `Arr::splitter()`. The splitter acts
/// as an array with methods specific to its usage. The intended use is for
/// wrapping a mutable `Arr` reference along with an element to be added to
/// the internal `Arr` after it has been split. The internal array can be filled
/// to capacity - the element won't be added to it until either `.consolidate()`
/// is invoked, or the instance goes out of scope.
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

    /// Splits the array at `i` as if the floating element were already
    /// inserted into the internal array. A new instance of a splitter is
    /// returned holding the rightmost values. The returned splitter holds a
    /// concrete instance of `Arr` that can be obtained by calling 
    /// `.into_inner()`.
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

    /// Pops items off the end of the splitter's array. It behaves as if the
    /// floating element has already been added to the internal `Arr`.
    /// 
    pub(crate) fn pop(&mut self) -> T {
        if self.elm.is_some() && self.pos == self.arr.len() {
            self.elm.take().unwrap()
        } else {
            self.arr.raw_pop()
        }
    }

    /// Consumes the splitter returning the inner `Arr` instance. This can only
    /// be invoked on a splitter returned by `.split_at()`, which holds a 
    /// non-reference instance.
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
    /// `Arr` instance. This should not be called prior to splitting as it will
    /// attempt to insert the floating element into an already full `Arr` and
    /// cause a panic.
    /// 
    fn consolidate(&mut self) {
        if self.elm.is_some() {
            self.arr.insert(self.pos, self.elm.take().unwrap());
        }
    }
}

impl<'a, T, const S: usize> Drop for ArrSplitter<'a, T, S> 
where
    T: Default,
{
    /// Called when a splitter instance is dropped. This method is called and 
    /// ensures the internal floating element is inserted into the wrapped 
    /// `Arr`.
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
