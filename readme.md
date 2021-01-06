[![Documentation](https://docs.rs/stadium/badge.svg)](https://docs.rs/stadium/)
[![Crates.io](https://img.shields.io/crates/v/stadium.svg)](https://crates.io/crates/stadium)


`stadium` provides the `Stadium` structure. This datastructure allows you to allocate any given set of objects (that can be of different types) in a continuous chunk of the memory.

## Example

```rust
// The first step is to build the stadium using a builder.
// This registers the data that will be used inside of the stadium.
let mut builder = stadium::builder();

let h_vec = builder.insert(vec![2019, 2020, 2021]);
let h_str = builder.insert("Hello, world!");
let h_int_a = builder.insert(68u64);
let h_int_b = builder.insert(65u64)

// Once the initialization is done, the actual stadium can be created.
let mut stadium = builder.build();

// Values can be retreived.
assert_eq!(&stadium[h_vec], &[2019, 2020, 2021][..]);
assert_eq!(stadium[h_str], "Hello, world!");
assert_eq!(stadium[h_int_a], 68);

// Or mutated.
stadium[h_vec].push(2022);
stadium[h_int_b] = 70;

// Other operations are supported.
assert_eq!(stadium.replace(h_str, "FOOBAR"), "Hello, world!");

stadium.swap(h_int_a, h_int_b);
assert_eq!(stadium[h_int_a], 70);
assert_eq!(stadium[h_int_b], 68);
```