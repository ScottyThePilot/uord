extern crate uord;

use uord::{UOrd2, UOrdProxied2};
use uord::proxy::TotalOrdFloat;



type UOrd2OfF32 = UOrdProxied2<f32, TotalOrdFloat>;



#[test]
fn main() {
  let a = UOrd2::new([0, 1]);
  let b = UOrd2::new([1, 0]);

  assert!(a.contains(&0));
  assert!(a.contains(&1));

  assert!(b.contains(&0));
  assert!(b.contains(&1));

  assert_eq!(a, b);

  let c = UOrd2::new([1, 1]);

  assert!(!c.is_distinct());

  let a = UOrd2OfF32::new_proxied([0.0, 1.0]);
  let b = UOrd2OfF32::new_proxied([1.0, 0.0]);

  assert!(a.contains_proxied(&0.0));
  assert!(a.contains_proxied(&1.0));

  assert!(b.contains_proxied(&0.0));
  assert!(b.contains_proxied(&1.0));

  assert_eq!(a, b);

  let c = UOrd2OfF32::new_proxied([1.0, 1.0]);

  assert!(!c.is_distinct());
}
