//! Structs and traits through which you can customize the implementations
//! of [`Ord`] and [`PartialEq`] used for types in [`UOrd`][super::UOrd].

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;



/// Provides an interface through which you can provide custom implementations
/// of [`Ord`] and [`PartialEq`] for foreign types which may not implement [`Ord`]
/// or only implement [`PartialOrd`].
///
/// Implementations of [`Proxy`] should:
/// - Adhere to the same rules as [`Ord`] and [`Eq`].
/// - Ideally not violate the relationship between [`Eq`] and [`Hash`].
/// - Maintain the equivalency of comparison implementations between types implementing [`Borrow`][core::borrow::Borrow].
///
/// One example of a type which benefits from this feature is `glam`'s integer vector types
/// which implement neither ordering trait (for valid reasons), but prevents [`UOrd`][super::UOrd] from
/// being usable with them.
///
/// Proxies are never instantiated, so they may be unit types or empty enums.
pub trait Proxy<T: ?Sized> {
  /// See [`Ord::cmp`].
  fn cmp(lhs: &T, rhs: &T) -> Ordering;

  /// See [`PartialEq::eq`].
  ///
  /// The default implementation returns `true` when [`Proxy::cmp`] returns [`Ordering::Equal`].
  fn eq(lhs: &T, rhs: &T) -> bool {
    matches!(Self::cmp(lhs, rhs), Ordering::Equal)
  }

  /// See [`PartialEq::ne`].
  ///
  /// The default implementation returns the inverse of [`Proxy::eq`].
  fn ne(lhs: &T, rhs: &T) -> bool {
    !Self::eq(lhs, rhs)
  }

  /// A utility function for wrapping a value with [`ProxyWrapper::new`].
  #[inline]
  fn wrap(value: T) -> ProxyWrapper<T, Self> where T: Sized {
    ProxyWrapper::new(value)
  }
}

/// The default proxy, implemented where `T: Ord`.
impl<T> Proxy<T> for ()
where T: ?Sized + Ord {
  #[inline]
  fn cmp(lhs: &T, rhs: &T) -> Ordering {
    Ord::cmp(lhs, rhs)
  }

  #[inline]
  fn eq(lhs: &T, rhs: &T) -> bool {
    PartialEq::eq(lhs, rhs)
  }
}



/// A wrapper type which implements [`Ord`] and [`Eq`] based on a specified [`Proxy`].
#[repr(transparent)]
pub struct ProxyWrapper<T: ?Sized, P: Proxy<T> + ?Sized> {
  #[allow(missing_docs)]
  pub phantom: PhantomData<P>,
  /// The inner value of this [`ProxyWrapper`].
  pub inner: T
}

impl<T, P: Proxy<T> + ?Sized> ProxyWrapper<T, P> {
  /// Create a new [`ProxyWrapper`].
  #[inline]
  pub const fn new(inner: T) -> Self {
    ProxyWrapper { inner, phantom: PhantomData }
  }

  /// Convert this [`ProxyWrapper`] into its inner type.
  pub const fn into_inner(self) -> T {
    unsafe { crate::transmute::transmute::<ProxyWrapper<T, P>, T>(self) }
  }

  /// Convert a slice of `T` into a slice of [`ProxyWrapper`].
  pub const fn wrap_slice(s: &[T]) -> &[Self] {
    unsafe { crate::transmute::transmute_slice::<T, Self>(s) }
  }

  /// Convert a mutable slice of `T` into a mutable slice of [`ProxyWrapper`].
  pub const fn wrap_slice_mut(s: &mut [T]) -> &mut [Self] {
    unsafe { crate::transmute::transmute_slice_mut::<T, Self>(s) }
  }

  /// Convert an array of `T` into an array of [`ProxyWrapper`].
  pub const fn wrap_array<const N: usize>(s: [T; N]) -> [Self; N] {
    unsafe { crate::transmute::transmute::<[T; N], [Self; N]>(s) }
  }

  /// Convert a reference to an array of `T` into a reference to an array of [`ProxyWrapper`].
  pub const fn wrap_array_ref<const N: usize>(s: &[T; N]) -> &[Self; N] {
    unsafe { crate::transmute::transmute_ref::<[T; N], [Self; N]>(s) }
  }

  /// Convert a mutable reference to an array of `T` into a mutable reference to an array of [`ProxyWrapper`].
  pub const fn wrap_array_ref_mut<const N: usize>(s: &mut [T; N]) -> &mut [Self; N] {
    unsafe { crate::transmute::transmute_ref_mut::<[T; N], [Self; N]>(s) }
  }

  /// Convert a slice of [`ProxyWrapper`] into a slice of `T`.
  pub const fn peel_slice(s: &[Self]) -> &[T] {
    unsafe { crate::transmute::transmute_slice::<Self, T>(s) }
  }

  /// Convert a mutable slice of [`ProxyWrapper`] into a mutable slice of `T`.
  pub const fn peel_slice_mut(s: &mut [Self]) -> &mut [T] {
    unsafe { crate::transmute::transmute_slice_mut::<Self, T>(s) }
  }

  /// Convert an array of [`ProxyWrapper`] into an array of `T`.
  pub const fn peel_array<const N: usize>(s: [Self; N]) -> [T; N] {
    unsafe { crate::transmute::transmute::<[Self; N], [T; N]>(s) }
  }

  /// Convert a reference to an array of [`ProxyWrapper`] into a reference to an array of `T`.
  pub const fn peel_array_ref<const N: usize>(s: &[Self; N]) -> &[T; N] {
    unsafe { crate::transmute::transmute_ref::<[Self; N], [T; N]>(s) }
  }

  /// Convert a mutable reference to an array of [`ProxyWrapper`] into a mutable reference to an array of `T`.
  pub const fn peel_array_ref_mut<const N: usize>(s: &mut [Self; N]) -> &mut [T; N] {
    unsafe { crate::transmute::transmute_ref_mut::<[Self; N], [T; N]>(s) }
  }
}

impl<T: ?Sized, P: Proxy<T> + ?Sized> ProxyWrapper<T, P> {
  /// Convert a reference to a `T` into a reference to a [`ProxyWrapper`].
  pub const fn wrap_ref(s: &T) -> &Self {
    unsafe { crate::transmute::transmute_ref::<T, Self>(s) }
  }

  /// Convert a mutable reference to a `T` into a mutable reference to a [`ProxyWrapper`].
  pub const fn wrap_ref_mut(s: &mut T) -> &mut Self {
    unsafe { crate::transmute::transmute_ref_mut::<T, Self>(s) }
  }

  /// Convert a reference to a [`ProxyWrapper`] into a reference to a `T`.
  #[inline]
  pub const fn peel_ref(s: &Self) -> &T {
    &s.inner
  }

  /// Convert a mutable reference to a [`ProxyWrapper`] into a mutable reference to a `T`.
  #[inline]
  pub const fn peel_ref_mut(s: &mut Self) -> &mut T {
    &mut s.inner
  }
}

impl<T: fmt::Debug, P: Proxy<T> + ?Sized> fmt::Debug for ProxyWrapper<T, P> {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.inner.fmt(f)
  }
}

impl<T: fmt::Display, P: Proxy<T> + ?Sized> fmt::Display for ProxyWrapper<T, P> {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.inner.fmt(f)
  }
}

impl<T: Copy, P: Proxy<T> + ?Sized> Copy for ProxyWrapper<T, P> {}

impl<T: Clone, P: Proxy<T> + ?Sized> Clone for ProxyWrapper<T, P> {
  #[inline]
  fn clone(&self) -> Self {
    ProxyWrapper::new(self.inner.clone())
  }
}

impl<T, P: Proxy<T> + ?Sized> PartialEq for ProxyWrapper<T, P> {
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    P::eq(&self.inner, &other.inner)
  }

  #[inline]
  fn ne(&self, other: &Self) -> bool {
    P::ne(&self.inner, &other.inner)
  }
}

impl<T, P: Proxy<T> + ?Sized> Eq for ProxyWrapper<T, P> {}

impl<T, P: Proxy<T> + ?Sized> PartialOrd for ProxyWrapper<T, P> {
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(ProxyWrapper::cmp(self, other))
  }
}

impl<T, P: Proxy<T> + ?Sized> Ord for ProxyWrapper<T, P> {
  #[inline]
  fn cmp(&self, other: &Self) -> Ordering {
    P::cmp(&self.inner, &other.inner)
  }
}

impl<T: Default, P: Proxy<T> + ?Sized> Default for ProxyWrapper<T, P> {
  fn default() -> Self {
    ProxyWrapper::new(T::default())
  }
}

impl<T: Hash, P: Proxy<T> + ?Sized> Hash for ProxyWrapper<T, P> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.inner.hash(state);
  }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<T, P: Proxy<T>> serde::Serialize for ProxyWrapper<T, P>
where T: serde::Serialize {
  #[inline]
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where S: serde::Serializer {
    T::serialize(&self.inner, serializer)
  }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de, T, P: Proxy<T>> serde::Deserialize<'de> for ProxyWrapper<T, P>
where T: serde::Deserialize<'de> + Ord {
  #[inline]
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where D: serde::Deserializer<'de> {
    T::deserialize(deserializer).map(ProxyWrapper::new)
  }
}



/// A [`Proxy`] for [`f32`] and [`f64`] that performs comparison based on
/// the [`f32::total_cmp`] and [`f64::total_cmp`] functions, respectively.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct TotalOrdFloat {}

impl Proxy<f64> for TotalOrdFloat {
  #[inline]
  fn cmp(lhs: &f64, rhs: &f64) -> Ordering {
    f64::total_cmp(lhs, rhs)
  }
}

impl Proxy<f32> for TotalOrdFloat {
  #[inline]
  fn cmp(lhs: &f32, rhs: &f32) -> Ordering {
    f32::total_cmp(lhs, rhs)
  }
}

/// A [`Proxy`] for types that implement `AsRef<[T]>`, performing
/// comparison based on `&[T]`'s [`Ord`] implementation.
///
/// Alternatively, a [`Proxy`] parameter may be supplied to
/// override `T`'s [`Ord`] implementation.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct OrdSliceLike<Slice, T, P = ()>
where Slice: AsRef<[T]>, P: Proxy<T> + ?Sized {
  slice: PhantomData<Slice>,
  value: PhantomData<T>,
  proxy: PhantomData<P>
}

impl<Slice, T, P> OrdSliceLike<Slice, T, P>
where Slice: AsRef<[T]>, P: Proxy<T> + ?Sized {
  #[inline]
  fn get_proxy_wrapper_slice(slice: &Slice) -> &[ProxyWrapper<T, P>] {
    ProxyWrapper::wrap_slice(slice.as_ref())
  }
}

impl<Slice, T, P> Proxy<Slice> for OrdSliceLike<Slice, T, P>
where Slice: AsRef<[T]>, P: Proxy<T> + ?Sized {
  fn cmp(lhs: &Slice, rhs: &Slice) -> Ordering {
    Ord::cmp(Self::get_proxy_wrapper_slice(lhs), Self::get_proxy_wrapper_slice(rhs))
  }

  fn eq(lhs: &Slice, rhs: &Slice) -> bool {
    Self::get_proxy_wrapper_slice(lhs) == Self::get_proxy_wrapper_slice(rhs)
  }

  fn ne(lhs: &Slice, rhs: &Slice) -> bool {
    Self::get_proxy_wrapper_slice(lhs) != Self::get_proxy_wrapper_slice(rhs)
  }
}
