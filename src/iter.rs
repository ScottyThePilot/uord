use crate::proxy::{ProxyWrapper, Proxy};

use core::iter::FusedIterator;



macro_rules! impl_iterator_functions {
  (Iterator $(, $map_function:expr)?) => {
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
      self.inner.next()$(.map($map_function))?
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
      self.inner.size_hint()
    }

    #[inline]
    fn fold<A, F>(self, init: A, f: F) -> A
    where F: FnMut(A, Self::Item) -> A, {
      self.inner$(.map($map_function))?.fold(init, f)
    }

    #[inline]
    fn count(self) -> usize {
      self.inner.count()
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
      self.inner.last()$(.map($map_function))?
    }
  };
  (DoubleEndedIterator $(, $map_function:expr)?) => {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
      self.inner.next_back()$(.map($map_function))?
    }

    #[inline]
    fn rfold<A, F>(self, init: A, f: F) -> A
    where F: FnMut(A, Self::Item) -> A, {
      self.inner$(.map($map_function))?.rfold(init, f)
    }
  };
  (ExactSizeIterator $(, $map_function:expr)?) => {
    #[inline]
    fn len(&self) -> usize {
      self.inner.len()
    }
  };
}

/// An iterator over references to each element of a [`UOrd`][crate::UOrd].
#[derive(Debug, Clone)]
pub struct UOrdIter<'a, T, const N: usize> {
  inner: <&'a [T; N] as IntoIterator>::IntoIter
}

impl<'a, T, const N: usize> UOrdIter<'a, T, N> {
  pub(crate) fn new(inner: &'a [T; N]) -> Self {
    UOrdIter { inner: inner.into_iter() }
  }
}

impl<'a, T, const N: usize> Iterator for UOrdIter<'a, T, N> {
  type Item = &'a T;

  impl_iterator_functions!(Iterator);
}

impl<'a, T, const N: usize> DoubleEndedIterator for UOrdIter<'a, T, N> {
  impl_iterator_functions!(DoubleEndedIterator);
}

impl<'a, T, const N: usize> ExactSizeIterator for UOrdIter<'a, T, N> {
  impl_iterator_functions!(ExactSizeIterator);
}

impl<'a, T, const N: usize> FusedIterator for UOrdIter<'a, T, N> {}

/// An iterator over each element of a [`UOrd`][crate::UOrd].
#[derive(Debug, Clone)]
pub struct UOrdIntoIter<T, const N: usize> {
  inner: <[T; N] as IntoIterator>::IntoIter
}

impl<T, const N: usize> UOrdIntoIter<T, N> {
  pub(crate) fn new(inner: [T; N]) -> Self {
    UOrdIntoIter { inner: inner.into_iter() }
  }
}

impl<T, const N: usize> Iterator for UOrdIntoIter<T, N> {
  type Item = T;

  impl_iterator_functions!(Iterator);
}

impl<T, const N: usize> DoubleEndedIterator for UOrdIntoIter<T, N> {
  impl_iterator_functions!(DoubleEndedIterator);
}

impl<T, const N: usize> ExactSizeIterator for UOrdIntoIter<T, N> {
  impl_iterator_functions!(ExactSizeIterator);
}

impl<T, const N: usize> FusedIterator for UOrdIntoIter<T, N> {}

/// An iterator over references to each element of a [`UOrdProxied`][crate::UOrdProxied], stripped of their wrappers.
#[derive(Debug, Clone)]
pub struct UOrdProxiedIter<'a, T, const N: usize, P: Proxy<T>> {
  inner: <&'a [ProxyWrapper<T, P>; N] as IntoIterator>::IntoIter
}

impl<'a, T, const N: usize, P: Proxy<T>> UOrdProxiedIter<'a, T, N, P> {
  pub(crate) fn new(inner: &'a [ProxyWrapper<T, P>; N]) -> Self {
    UOrdProxiedIter { inner: inner.into_iter() }
  }
}

impl<'a, T, const N: usize, P: Proxy<T>> Iterator for UOrdProxiedIter<'a, T, N, P> {
  type Item = &'a T;

  impl_iterator_functions!(Iterator, ProxyWrapper::peel_ref);
}

impl<'a, T, const N: usize, P: Proxy<T>> DoubleEndedIterator for UOrdProxiedIter<'a, T, N, P> {
  impl_iterator_functions!(DoubleEndedIterator, ProxyWrapper::peel_ref);
}

impl<'a, T, const N: usize, P: Proxy<T>> ExactSizeIterator for UOrdProxiedIter<'a, T, N, P> {
  impl_iterator_functions!(ExactSizeIterator, ProxyWrapper::peel_ref);
}

impl<'a, T, const N: usize, P: Proxy<T>> FusedIterator for UOrdProxiedIter<'a, T, N, P> {}

/// An iterator over each element of a [`UOrdProxied`][crate::UOrdProxied], stripped of their wrappers.
#[derive(Debug, Clone)]
pub struct UOrdProxiedIntoIter<T, const N: usize, P: Proxy<T>> {
  inner: <[ProxyWrapper<T, P>; N] as IntoIterator>::IntoIter
}

impl<T, const N: usize, P: Proxy<T>> UOrdProxiedIntoIter<T, N, P> {
  pub(crate) fn new(inner: [ProxyWrapper<T, P>; N]) -> Self {
    UOrdProxiedIntoIter { inner: inner.into_iter() }
  }
}

impl<T, const N: usize, P: Proxy<T>> Iterator for UOrdProxiedIntoIter<T, N, P> {
  type Item = T;

  impl_iterator_functions!(Iterator, ProxyWrapper::into_inner);
}

impl<T, const N: usize, P: Proxy<T>> DoubleEndedIterator for UOrdProxiedIntoIter<T, N, P> {
  impl_iterator_functions!(DoubleEndedIterator, ProxyWrapper::into_inner);
}

impl<T, const N: usize, P: Proxy<T>> ExactSizeIterator for UOrdProxiedIntoIter<T, N, P> {
  impl_iterator_functions!(ExactSizeIterator, ProxyWrapper::into_inner);
}

impl<T, const N: usize, P: Proxy<T>> FusedIterator for UOrdProxiedIntoIter<T, N, P> {}
