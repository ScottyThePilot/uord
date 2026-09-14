extern crate glam;
extern crate uord;

use uord::UOrdProxied2;
use uord::proxy::{OrdArrayLike, TotalOrdFloat};
use glam::{UVec2, Vec2};



type UVec2Proxy = OrdArrayLike<UVec2, u32, 2>;
type Vec2Proxy = OrdArrayLike<Vec2, f32, 2, TotalOrdFloat>;

type UOrd2OfUVec2 = UOrdProxied2<UVec2, UVec2Proxy>;
type UOrd2OfVec2 = UOrdProxied2<Vec2, Vec2Proxy>;



#[test]
fn main() {
  let a = UOrd2OfUVec2::new_proxied([UVec2::ZERO, UVec2::ONE]);
  let b = UOrd2OfUVec2::new_proxied([UVec2::ONE, UVec2::ZERO]);

  assert!(a.contains_proxied(&UVec2::ZERO));
  assert!(a.contains_proxied(&UVec2::ONE));

  assert!(b.contains_proxied(&UVec2::ZERO));
  assert!(b.contains_proxied(&UVec2::ONE));

  assert_eq!(a, b);

  let c = UOrd2OfUVec2::new_proxied([UVec2::ONE, UVec2::ONE]);

  assert!(!c.is_distinct());

  let a = UOrd2OfVec2::new_proxied([Vec2::ZERO, Vec2::ONE]);
  let b = UOrd2OfVec2::new_proxied([Vec2::ONE, Vec2::ZERO]);

  assert!(a.contains_proxied(&Vec2::ZERO));
  assert!(a.contains_proxied(&Vec2::ONE));

  assert!(b.contains_proxied(&Vec2::ZERO));
  assert!(b.contains_proxied(&Vec2::ONE));

  assert_eq!(a, b);

  let c = UOrd2OfVec2::new_proxied([Vec2::ONE, Vec2::ONE]);

  assert!(!c.is_distinct());
}
