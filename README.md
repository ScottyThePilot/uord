# UOrd

[![Crate][crates-img]][crates-url]
[![Documentation][docs-img]][docs-url]

A library providing implementations of unordered pairs (or more generally, unordered sets).

This is useful when, for example, you want to create a HashMap that associates data with pairs of things:
```rust
use uord::UOrd2;
use std::collections::HashMap;
let mut map: HashMap<UOrd2<u32>, String> = HashMap::new();
map.insert(UOrd2::new([1, 6]), "1-6".to_owned());
map.insert(UOrd2::new([3, 5]), "3-5".to_owned());
map.insert(UOrd2::new([2, 4]), "2-4".to_owned());

assert!(map.contains_key(&UOrd2::new([1, 6])));
```

When creating a [`UOrd`], the ordering of the items on creation does not matter,
and [`UOrd`]s created with different initial element orders will be equal to one another.

[`UOrd`]: https://docs.rs/uord/latest/uord/struct.UOrd.html

[crates-img]: https://img.shields.io/crates/v/uord.svg
[crates-url]: https://crates.io/crates/uord

[docs-img]: https://docs.rs/uord/badge.svg
[docs-url]: https://docs.rs/uord
