use core::mem::ManuallyDrop;

macro_rules! assert_size_eq {
  ($Left:ty, $Right:ty) => (const {
    assert!(size_of::<$Left>() == size_of::<$Right>());
  });
}

macro_rules! assert_align_eq {
  ($Left:ty, $Right:ty) => (const {
    assert!(align_of::<$Left>() == align_of::<$Right>());
  });
}



pub(crate) const unsafe fn transmute_ref<T: ?Sized, U: ?Sized>(ptr: &T) -> &U {
  assert_size_eq!(*const T, *const U);

  unsafe { &*transmute::<*const T, *const U>(ptr as *const T) }
}

pub(crate) const unsafe fn transmute_ref_mut<T: ?Sized, U: ?Sized>(ptr: &mut T) -> &mut U {
  assert_size_eq!(*mut T, *mut U);

  unsafe { &mut *transmute::<*mut T, *mut U>(ptr as *mut T) }
}

pub(crate) const unsafe fn transmute_slice<T, U>(slice: &[T]) -> &[U] {
  assert_size_eq!(T, U);
  assert_align_eq!(T, U);

  unsafe { core::slice::from_raw_parts(slice.as_ptr() as *const U, slice.len()) }
}

pub(crate) const unsafe fn transmute_slice_mut<T, U>(slice: &mut [T]) -> &mut [U] {
  assert_size_eq!(T, U);
  assert_align_eq!(T, U);

  unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut U, slice.len()) }
}

pub(crate) const unsafe fn transmute<T, U>(value: T) -> U {
  assert_size_eq!(T, U);
  assert_align_eq!(T, U);

  #[repr(C)]
  union transmuteCast<T, U> {
    t: ManuallyDrop<T>,
    u: ManuallyDrop<U>
  }

  let value = ManuallyDrop::new(value);
  ManuallyDrop::into_inner(unsafe {
    transmuteCast { t: value }.u
  })
}
