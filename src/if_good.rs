
use std::marker::Sized;

/// Trait to add methods to `Result` that adds methods similar to `.map()`
/// and `.map_or_else()`, but don't return a value.
///
pub(crate) trait IfOK<T, E> {
    fn if_ok<F>(self, _f: F)
    where 
        F: FnMut(T),
        Self: Sized;

    fn if_ok_else<F, G>(self, _f: F, _g: G) 
    where
        F: FnMut(T),
        G: FnMut(E),
        Self: Sized;
}

/// Trait to add methods to `Option` similar to `.map()` and `.map_or_else()`
/// but don't return a value.
///
pub(crate) trait IfSome<T> {
    fn if_some<F>(self, _f: F)
    where 
        F: FnMut(T),
        Self: Sized;

    fn if_some_else<F, G>(self, _f: F, _g: G)
    where
        F: FnMut(T),
        G: FnMut(),
        Self: Sized;
}

impl<T> IfSome<T> for Option<T> {
    /// When applied to an `Option`, the provided callback is called when
    /// the `Option` is the `Some` variant, passing its wrapped value to  the
    /// callback.
    ///
    fn if_some<F>(self, mut f: F)
    where 
        F: FnMut(T),
    {
        if let Some(v) = self { f(v); }
    }

    /// Similar to `.map_or_else()`. When the `Option` is of the `Some` variant,
    /// the closure, `f()` will be invoked with the value, consuming it.
    /// When an `Option` is of the `None` variant, `g()` is invoked which takes
    /// no parameters.
    /// 
    fn if_some_else<F, G>(self, mut f: F, mut g: G) 
    where 
        F: FnMut(T),
        G: FnMut(),
    {
        match self {
            Some(v) => f(v),
            None    => g(),
        }
    }
}

impl<T, E> IfOK<T, E> for Result<T, E> {
    /// When applied to a `Result`, the provided callback is called when
    /// the `Result` is the `Ok` variant, passing its wrapped value to  the
    /// callback.
    ///
    fn if_ok<F>(self, mut f: F) 
    where 
        F: FnMut(T),
    {
        if let Ok(v) = self { f(v); }
    }

    /// IF the `Result` this is invoked on is `Ok`, `f()` is invoked with the
    /// value, consuming it. If the `Result` is the `Err` variant, `g()` is
    /// invoked passing to it the error value, consuming it.
    /// 
    fn if_ok_else<F, G>(self, mut f: F, mut g: G) 
    where 
        F: FnMut(T),
        G: FnMut(E),
    {
        match self {
            Ok(v)  => f(v),
            Err(e) => g(e),
        }
    }
}
