# UOrd

A library providing implementations of unordered pairs (or more generally, unordered sets).

This is useful when, for example, you want to create a HashMap that associates data with pairs of things:
```rust
use uord::UOrd2;
use std::collections::HashMap;
let mut map: HashMap<UOrd2<u16>, String> = HashMap::new();
map.insert(UOrd2::new([1, 6]), "1-6".to_owned());
map.insert(UOrd2::new([3, 5]), "3-5".to_owned());
map.insert(UOrd2::new([2, 4]), "2-4".to_owned());
```

When creating a [`UOrd`], the ordering of the items on creation does not matter,
and [`UOrd`]s created with different initial element orders will be equal to one another.
