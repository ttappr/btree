
use std::marker::Sized;

/// Trait to add methods to `Option` and `Result` that get called when the
/// respective values of each are `Some` and `Ok`. The callback returns no
/// value, but otherwise similar to `.map()`.
///
pub(crate) trait IFGood<T> {
    fn if_ok<F>(self, mut _f: F)
    where 
        F: FnMut(T),
        Self: Sized,
    {
        unimplemented!();
    }
    fn if_some<F>(self, mut _f: F)
    where 
        F: FnMut(T),
        Self: Sized,
    {
        unimplemented!();
    }
}

impl<T> IFGood<T> for Option<T> {
    /// When appied to an `Option`, the provided callback is called when
    /// the `Option` is the `Some` variant, passing its wrapped value to  the
    /// callback.
    ///
    fn if_some<F>(self, mut f: F)
    where 
        F: FnMut(T),
    {
        if let Some(v) = self { f(v); }
    }
}

impl<T, E> IFGood<T> for Result<T, E> {
    /// When appied to a `Result`, the provided callback is called when
    /// the `Result` is the `Ok` variant, passing its wrapped value to  the
    /// callback.
    ///
    fn if_ok<F>(self, mut f: F) 
    where 
        F: FnMut(T),
    {
        if let Ok(v) = self { f(v); }
    }
}
