#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
  absolute_paths_not_starting_with_crate,
  redundant_imports,
  redundant_lifetimes,
  future_incompatible,
  deprecated_in_future,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  unnameable_types,
  unreachable_pub
)]

//! A library providing implementations of unordered pairs (or more generally, unordered sets).
//!
//! This is useful when, for example, you want to create a HashMap that associates data with pairs of things:
//! ```rust
//! #use uord::UOrd2;
//! #use std::collections::HashMap;
//! let mut map: HashMap<UOrd2<u16>, String> = HashMap::new();
//! map.insert(UOrd2::new([1, 6]), "1-6".to_owned());
//! map.insert(UOrd2::new([3, 5]), "3-5".to_owned());
//! map.insert(UOrd2::new([2, 4]), "2-4".to_owned());
//! ```
//!
//! When creating a [`UOrd`], the ordering of the items on creation does not matter,
//! and [`UOrd`]s created with different initial element orders will be equal to one another.

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
extern crate serde;

#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[cfg(feature = "alloc")]
extern crate alloc;

mod iter;
pub mod proxy;
mod transmute;

pub use crate::iter::*;
use crate::proxy::{Proxy, ProxyWrapper};

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};

#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[cfg(feature = "alloc")]
use alloc::vec::Vec;



/// An unordered tuple of items of type `T` and length 2.
pub type UOrd2<T> = UOrd<T, 2>;
/// An unordered tuple of items of type `T` and length 3.
pub type UOrd3<T> = UOrd<T, 3>;
/// An unordered tuple of items of type `T` and length 4.
pub type UOrd4<T> = UOrd<T, 4>;
/// An unordered tuple of items of type `T` and length 5.
pub type UOrd5<T> = UOrd<T, 5>;
/// An unordered tuple of items of type `T` and length 6.
pub type UOrd6<T> = UOrd<T, 6>;

/// An unordered tuple of items of type `T` and length `N`.
///
/// [`UOrd`]'s implementation maintains a sorted list of values that is not allowed
/// to be mutated. Using interior mutability to mutate elements of a [`UOrd`] is a logic error
/// and is not supported. Doing so is very likely to cause strange behavior.
#[repr(transparent)]
pub struct UOrd<T, const N: usize> {
  values: [T; N]
}

impl<T, const N: usize> UOrd<T, N> where T: Ord {
  /// Create a new [`UOrd`] from an array of values.
  pub fn new(mut values: [T; N]) -> Self {
    values.sort_unstable();
    UOrd { values }
  }

  /// Tests whether this [`UOrd`] contains the given value.
  pub fn contains<Q: ?Sized>(&self, x: &Q) -> bool
  where T: Borrow<Q>, Q: Eq {
    self.test_any(|value| value.borrow() == x)
  }

  /// Replaces any occurance of `from` with `to`, creating a new [`UOrd`].
  pub fn replace<Q: ?Sized>(&self, from: &Q, to: &T) -> Self
  where T: Borrow<Q> + Clone, Q: Eq {
    self.map_each_ref(|value| {
      if value.borrow() == from {
        to.clone()
      } else {
        value.clone()
      }
    })
  }

  /// Applies the function `f` to each element of this [`UOrd`], returning a new [`UOrd`].
  pub fn map<U>(self, f: impl FnMut(T) -> U) -> UOrd<U, N> where U: Ord {
    UOrd::new(self.into_array().map(f))
  }

  /// Applies the function `f` to a reference to each element of this [`UOrd`], returning a new [`UOrd`].
  pub fn map_each_ref<U>(&self, f: impl FnMut(&T) -> U) -> UOrd<U, N> where U: Ord {
    UOrd::new(self.as_ref_array().map(f))
  }

  /// Applies a fallible function `f` to each element of this [`UOrd`], returning a value of type `Option<UOrd<U, N>>`.
  /// The provided function takes a `T` and must return a value of type `Option<U>`.
  ///
  /// This function is temporary, and will be deprecated when `try_trait_v2` is stabilized.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_map_opt<U>(self, f: impl FnMut(T) -> Option<U>) -> Option<UOrd<U, N>> where U: Ord {
    self.into_array().into_iter().map(f).collect::<Option<Vec<U>>>()
      .map(|list| <[U; N]>::try_from(list).unwrap_or_else(|_| unreachable!()))
      .map(UOrd::new)
  }

  /// Applies a fallible function `f` to each element of this [`UOrd`], returning a value of type `Result<UOrd<U, N>, E>`.
  /// The provided function takes a `T` and must return a value of type `Return<U, E>`.
  ///
  /// This function is temporary, and will be deprecated when `try_trait_v2` is stabilized.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_map_res<U, E>(self, f: impl FnMut(T) -> Result<U, E>) -> Result<UOrd<U, N>, E> where U: Ord {
    self.into_array().into_iter().map(f).collect::<Result<Vec<U>, E>>()
      .map(|list| <[U; N]>::try_from(list).unwrap_or_else(|_| unreachable!()))
      .map(UOrd::new)
  }

  /// Converts each element of this [`UOrd`] into a given type `U`
  /// based on `T`'s `Into<U>` implementation.
  pub fn convert<U>(self) -> UOrd<U, N>
  where T: Into<U>, U: Ord {
    self.map(T::into)
  }

  /// Fallibly converts each element of this [`UOrd`] into a given type `U`
  /// based on `T`'s `TryInto<U>` implementation, alternatively returning error.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_convert<U>(self) -> Result<UOrd<U, N>, T::Error>
  where T: TryInto<U>, U: Ord {
    self.try_map_res(T::try_into)
  }

  /// Tests if all elements pass the given predicate.
  ///
  /// Equivalent to `self.iter().all(f)`.
  pub fn test_all(&self, f: impl FnMut(&T) -> bool) -> bool {
    self.iter().all(f)
  }

  /// Tests if any element passes the given predicate.
  ///
  /// Equivalent to `self.iter().any(f)`.
  pub fn test_any(&self, f: impl FnMut(&T) -> bool) -> bool {
    self.iter().any(f)
  }

  /// Converts this [`UOrd`] into a [`UOrdProxied`] by wrapping its contained elements of type `T`
  /// in [`ProxyWrapper`]s, using the provided [`Proxy`] `P` for comparison and equality.
  pub fn make_proxied<P: Proxy<T>>(self) -> UOrdProxied<T, N, P> {
    UOrdProxied::new_proxied(self.into_array())
  }
}

impl<T, const N: usize> UOrd<T, N> {
  /// Gets the first (smallest) element in the internal list.
  ///
  /// # Panics
  /// This function will panic if `N == 0`.
  pub const fn min(&self) -> &T {
    self.values.first().expect("uord length must not be 0")
  }

  /// Gets the last (greatest) element in the internal list.
  ///
  /// # Panics
  /// This function will panic if `N == 0`.
  pub const fn max(&self) -> &T {
    self.values.last().expect("uord length must not be 0")
  }

  /// Borrows each element in this [`UOrd`], returning a [`UOrd`] of those references.
  pub fn each_ref(&self) -> UOrd<&T, N> {
    // It is fine to directly instantiate a `UOrd` here since `T` and `&T`'s Ord
    // implementation are identical, thus sorting the list would be redundant.
    UOrd { values: self.as_ref_array() }
  }

  /// Borrows each element in this [`UOrd`], returning an array of those references.
  pub fn as_ref_array(&self) -> [&T; N] {
    self.values.each_ref()
  }

  /// Returns an immutable reference to the array of elements, which is sorted.
  #[inline]
  pub const fn as_array(&self) -> &[T; N] {
    &self.values
  }

  /// Converts this [`UOrd`] into its array of elements, which is sorted.
  pub const fn into_array(self) -> [T; N] {
    unsafe { crate::transmute::transmute::<Self, [T; N]>(self) }
  }

  /// Creates an iterator over references to each element of this [`UOrd`].
  #[inline]
  pub fn iter(&self) -> UOrdIter<'_, T, N> {
    self.into_iter()
  }
}

/// An unordered tuple of items of type `T` and length 2, additionally utilizing a [`Proxy`].
pub type UOrdProxied2<T, P> = UOrd2<ProxyWrapper<T, P>>;
/// An unordered tuple of items of type `T` and length 3, additionally utilizing a [`Proxy`].
pub type UOrdProxied3<T, P> = UOrd3<ProxyWrapper<T, P>>;
/// An unordered tuple of items of type `T` and length 4, additionally utilizing a [`Proxy`].
pub type UOrdProxied4<T, P> = UOrd4<ProxyWrapper<T, P>>;
/// An unordered tuple of items of type `T` and length 5, additionally utilizing a [`Proxy`].
pub type UOrdProxied5<T, P> = UOrd5<ProxyWrapper<T, P>>;
/// An unordered tuple of items of type `T` and length 6, additionally utilizing a [`Proxy`].
pub type UOrdProxied6<T, P> = UOrd6<ProxyWrapper<T, P>>;

/// An unordered tuple of items of type `T` and length `N`, additionally utilizing a [`Proxy`].
///
/// This is the same as `UOrd<ProxyWrapper<T, P>, N>` where `P` is a [`Proxy`], which customizes
/// the [`Ord`] and [`PartialEq`] implementations of [`ProxyWrapper`], modifying [`UOrd`]'s behavior.
pub type UOrdProxied<T, const N: usize, P> = UOrd<ProxyWrapper<T, P>, N>;

impl<T, const N: usize, P> UOrdProxied<T, N, P> where P: Proxy<T> {
  /// Create a new [`UOrdProxied`] from an array of values, utilizing a custom [`Proxy`] for comparison and equality.
  pub fn new_proxied(values: [T; N]) -> Self {
    UOrd::new(ProxyWrapper::wrap_array(values))
  }

  /// Tests whether this [`UOrdProxied`] contains the given value.
  pub fn contains_proxied<Q: ?Sized>(&self, x: &Q) -> bool
  where T: Borrow<Q>, for<'q> P: Proxy<&'q Q> {
    self.test_any_proxied(|value| P::wrap(value.borrow()) == P::wrap(x))
  }

  /// Replaces any occurance of `from` with `to`, creating a new [`UOrdProxied`].
  pub fn replace_proxied<Q: ?Sized>(&self, from: &Q, to: T) -> Self
  where T: Borrow<Q> + Clone, for<'q> P: Proxy<&'q Q> {
    self.map_each_ref_proxied(|value| {
      if P::wrap(value.borrow()) == P::wrap(from) {
        to.clone()
      } else {
        value.clone()
      }
    })
  }

  /// Borrows each element in this [`UOrdProxied`], returning a [`UOrd`] of those references, stripped of their wrappers.
  pub fn each_ref_proxied(&self) -> UOrd<&T, N> where T: Ord {
    UOrd::new(self.as_ref_array_proxied())
  }

  /// Borrows each element in this [`UOrdProxied`], returning an array of those references, stripped of their wrappers.
  pub fn as_ref_array_proxied(&self) -> [&T; N] {
    self.values.each_ref().map(ProxyWrapper::peel_ref)
  }

  /// Returns an immutable reference to the array of elements, which is sorted, and has each element stripped of their wrappers.
  pub const fn as_array_proxied(&self) -> &[T; N] {
    ProxyWrapper::peel_array_ref(self.as_array())
  }

  /// Converts this [`UOrdProxied`] into its array of elements, which is sorted, and has each element stripped of their wrappers.
  pub const fn into_array_proxied(self) -> [T; N] {
    ProxyWrapper::peel_array(self.into_array())
  }

  /// Applies the function `f` to each element of this [`UOrdProxied`], returning a new [`UOrdProxied`].
  /// This function also allows a proxy, `R`, for the new [`UOrdProxied`] to be specified.
  pub fn map_proxied<U, R>(self, f: impl FnMut(T) -> U) -> UOrdProxied<U, N, R> where R: Proxy<U> {
    UOrdProxied::new_proxied(self.into_array_proxied().map(f))
  }

  /// Applies the function `f` to a reference to each element of this [`UOrdProxied`], returning a new [`UOrdProxied`].
  /// This function also allows a proxy, `R`, for the new [`UOrdProxied`] to be specified.
  pub fn map_each_ref_proxied<U, R>(&self, f: impl FnMut(&T) -> U) -> UOrdProxied<U, N, R> where R: Proxy<U> {
    UOrdProxied::new_proxied(self.as_ref_array_proxied().map(f))
  }

  /// Applies a fallible function `f` to each element of this [`UOrdProxied`], returning a value of type `Option<UOrdProxied<U, N, R>>`.
  /// The provided function takes a `T` and must return a value of type `Option<U>`.
  /// This function also allows a proxy, `R`, for the new [`UOrdProxied`] to be specified.
  ///
  /// This function is temporary, and will be deprecated when `try_trait_v2` is stabilized.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_map_proxied_opt<U, R>(self, mut f: impl FnMut(T) -> Option<U>) -> Option<UOrdProxied<U, N, R>> where R: Proxy<U> {
    self.try_map_opt(|value| f(ProxyWrapper::into_inner(value)).map(ProxyWrapper::new))
  }

  /// Applies a fallible function `f` to each element of this [`UOrdProxied`], returning a value of type `Result<UOrdProxied<U, N, R>, E>`.
  /// The provided function takes a `T` and must return a value of type `Return<U, E>`.
  /// This function also allows a proxy, `R`, for the new [`UOrdProxied`] to be specified.
  ///
  /// This function is temporary, and will be deprecated when `try_trait_v2` is stabilized.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_map_proxied_res<U, R, E>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<UOrdProxied<U, N, R>, E> where R: Proxy<U> {
    self.try_map_res(|value| f(ProxyWrapper::into_inner(value)).map(ProxyWrapper::new))
  }

  /// Converts each element of this [`UOrdProxied`] into a given type `U`
  /// based on `T`'s `Into<U>` implementation.
  pub fn convert_proxied<U, R>(self) -> UOrdProxied<U, N, R>
  where T: Into<U>, R: Proxy<U> {
    self.map_proxied(T::into)
  }

  /// Fallibly converts each element of this [`UOrdProxied`] into a given type `U`
  /// based on `T`'s `TryInto<U>` implementation, alternatively returning error.
  #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
  #[cfg(feature = "alloc")]
  pub fn try_convert_proxied<U, R>(self) -> Result<UOrdProxied<U, N, R>, T::Error>
  where T: TryInto<U>, R: Proxy<U> {
    self.try_map_proxied_res(T::try_into)
  }

  /// Tests if all elements pass the given predicate.
  ///
  /// Equivalent to `self.iter_proxied().all(f)`.
  pub fn test_all_proxied(&self, f: impl FnMut(&T) -> bool) -> bool {
    self.iter_proxied().all(f)
  }

  /// Tests if any element passes the given predicate.
  ///
  /// Equivalent to `self.iter_proxied().any(f)`.
  pub fn test_any_proxied(&self, f: impl FnMut(&T) -> bool) -> bool {
    self.iter_proxied().any(f)
  }

  /// Converts this [`UOrdProxied`] into a [`UOrd`], unwrapping the contained
  /// [`ProxyWrapper`]s, using the default implementation of [`Ord`] on `T` for comparison and equality.
  pub fn make_unproxied(self) -> UOrd<T, N> where T: Ord {
    UOrd::new(self.into_array_proxied())
  }

  /// Creates an iterator over references to each element of this [`UOrdProxied`], stripped of their wrappers.
  #[inline]
  pub fn iter_proxied(&self) -> UOrdProxiedIter<'_, T, N, P> {
    UOrdProxiedIter::new(self.as_array())
  }

  /// Creates an iterator over each element of this [`UOrdProxied`], stripped of their wrappers.
  #[inline]
  pub fn into_iter_proxied(self) -> UOrdProxiedIntoIter<T, N, P> {
    UOrdProxiedIntoIter::new(self.into_array())
  }
}

impl<T> UOrd2<T> where T: Ord {
  /// Returns `true` if this pair was distinct (the values in it were not equal to each other) otherwise returns `false`.
  pub fn is_distinct(&self) -> bool {
    let [min, max] = self.as_array();
    min != max
  }

  /// If this unordered pair contains the given value, this function will return the other value.
  /// If this unordered pair did not contain the given value, this will return `None`.
  ///
  /// Note that this function does not care about the distinctness of the pair, and will
  /// still return the other value, even if it was equal to the input value.
  /// If you need this behavior, see [`UOrd::other_distinct`].
  pub fn other<Q: ?Sized>(&self, x: &Q) -> Option<&T>
  where T: Borrow<Q>, Q: Eq {
    let [min, max] = self.as_array();
    Option::or(
      if max.borrow() == x { Some(min) } else { None },
      if min.borrow() == x { Some(max) } else { None }
    )
  }

  /// If this unordered pair contains the given value, this function will return the other value.
  /// If this unordered pair did not contain the given value, this will return `None`.
  ///
  /// Additionally, this function will return `None` if the two items in this pair were equal,
  /// guaranteeing that the output value is never equal to the input value in the case of an indistinct pair.
  pub fn other_distinct<Q: ?Sized>(&self, x: &Q) -> Option<&T>
  where T: Borrow<Q>, Q: Eq {
    let [min, max] = self.as_array();
    Option::xor(
      if max.borrow() == x { Some(min) } else { None },
      if min.borrow() == x { Some(max) } else { None }
    )
  }
}

impl<T, P> UOrdProxied2<T, P> where P: Proxy<T> {
  /// If this unordered pair contains the given value, this function will return the other value.
  /// If this unordered pair did not contain the given value, this will return `None`.
  ///
  /// Note that this function does not care about the distinctness of the pair, and will
  /// still return the other value, even if it was equal to the input value.
  /// If you need this behavior, see [`UOrdProxied::other_distinct_proxied`].
  pub fn other_proxied<Q: ?Sized>(&self, x: &Q) -> Option<&T>
  where T: Borrow<Q>, for<'q> P: Proxy<&'q Q> {
    let [min, max] = self.as_array_proxied();
    Option::or(
      if P::wrap(max.borrow()) == P::wrap(x) { Some(min) } else { None },
      if P::wrap(min.borrow()) == P::wrap(x) { Some(max) } else { None }
    )
  }

  /// If this unordered pair contains the given value, this function will return the other value.
  /// If this unordered pair did not contain the given value, this will return `None`.
  ///
  /// Additionally, this function will return `None` if the two items in this pair were equal,
  /// guaranteeing that the output value is never equal to the input value in the case of an indistinct pair.
  pub fn other_distinct_proxied<Q: ?Sized>(&self, x: &Q) -> Option<&T>
  where T: Borrow<Q>, for<'q> P: Proxy<&'q Q> {
    let [min, max] = self.as_array_proxied();
    Option::xor(
      if P::wrap(max.borrow()) == P::wrap(x) { Some(min) } else { None },
      if P::wrap(min.borrow()) == P::wrap(x) { Some(max) } else { None }
    )
  }
}

impl<T: fmt::Display, const N: usize> fmt::Display for UOrd<T, N> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut d = f.debug_list();
    for value in self.values.iter() {
      d.entry(&format_args!("{value}"));
    };
    d.finish()
  }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for UOrd<T, N> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut d = f.debug_tuple("UOrd");
    for value in self.values.iter() {
      d.field(&value);
    };
    d.finish()
  }
}

impl<T, const N: usize> Copy for UOrd<T, N> where T: Copy {}

impl<T, const N: usize> Clone for UOrd<T, N> where T: Clone {
  fn clone(&self) -> Self {
    UOrd { values: self.values.clone() }
  }
}

impl<T, const N: usize> PartialEq for UOrd<T, N> where T: Ord {
  fn eq(&self, other: &Self) -> bool {
    self.as_array() == other.as_array()
  }
}

impl<T, const N: usize> Eq for UOrd<T, N> where T: Ord {}

impl<T, const N: usize> PartialOrd for UOrd<T, N> where T: Ord {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(Self::cmp(self, other))
  }
}

impl<T, const N: usize> Ord for UOrd<T, N> where T: Ord {
  fn cmp(&self, other: &Self) -> Ordering {
    Ord::cmp(self.as_array(), other.as_array())
  }
}

impl<T, const N: usize> Hash for UOrd<T, N> where T: Hash {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.as_array().hash(state);
  }
}

impl<T, const N: usize> From<[T; N]> for UOrd<T, N> where T: Ord {
  fn from(value: [T; N]) -> Self {
    UOrd::new(value)
  }
}

impl<T, const N: usize> From<UOrd<T, N>> for [T; N] {
  fn from(value: UOrd<T, N>) -> Self {
    value.into_array()
  }
}

macro_rules! impl_uord_tuple_conversion {
  ($T:ident, $N:literal, $Tuple:ty) => {
    impl<$T> From<$Tuple> for UOrd<$T, $N> where T: Ord {
      #[inline]
      fn from(value: $Tuple) -> UOrd<$T, $N> {
        UOrd::new(<[$T; $N]>::from(value))
      }
    }

    impl<$T> From<UOrd<$T, $N>> for $Tuple {
      #[inline]
      fn from(value: UOrd<$T, $N>) -> $Tuple {
        <$Tuple>::from(value.into_array())
      }
    }
  };
}

impl_uord_tuple_conversion!(T, 1, (T,));
impl_uord_tuple_conversion!(T, 2, (T, T));
impl_uord_tuple_conversion!(T, 3, (T, T, T));
impl_uord_tuple_conversion!(T, 4, (T, T, T, T));
impl_uord_tuple_conversion!(T, 5, (T, T, T, T, T));
impl_uord_tuple_conversion!(T, 6, (T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 7, (T, T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 8, (T, T, T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 9, (T, T, T, T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 10, (T, T, T, T, T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 11, (T, T, T, T, T, T, T, T, T, T, T));
impl_uord_tuple_conversion!(T, 12, (T, T, T, T, T, T, T, T, T, T, T, T));

impl<'a, T, const N: usize> IntoIterator for &'a UOrd<T, N> {
  type Item = &'a T;
  type IntoIter = UOrdIter<'a, T, N>;

  /// Creates an iterator over references to each element of this [`UOrd`].
  #[inline]
  fn into_iter(self) -> Self::IntoIter {
    UOrdIter::new(self.as_array())
  }
}

impl<T, const N: usize> IntoIterator for UOrd<T, N> {
  type Item = T;
  type IntoIter = UOrdIntoIter<T, N>;

  /// Creates an iterator over each element of this [`UOrd`].
  #[inline]
  fn into_iter(self) -> Self::IntoIter {
    UOrdIntoIter::new(self.into_array())
  }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<T, const N: usize> serde::Serialize for UOrd<T, N>
where T: serde::Serialize {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where S: serde::Serializer {
    <[T; N] as serde_big_array::BigArray<T>>::serialize(self.as_array(), serializer)
  }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de, T, const N: usize> serde::Deserialize<'de> for UOrd<T, N>
where T: serde::Deserialize<'de> + Ord {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where D: serde::Deserializer<'de> {
    <[T; N] as serde_big_array::BigArray<T>>::deserialize(deserializer).map(UOrd::new)
  }
}
