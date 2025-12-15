#![cfg_attr(not(feature = "std"), no_std)]
#![deny(missing_docs)]
//! Safe, non-panicking numeric primitives built on top of pure-Rust `num-bigint` (alloc-only).
//!
//! Enable the `std` feature to opt into `std` support for downstream consumers.

extern crate alloc;

#[cfg(any(test, feature = "std"))]
extern crate std;

/// Fixed-precision decimal support built on `SafeInt`.
pub mod decimal;
/// Arbitrary-precision integer support and helpers.
pub mod integer;
/// Parsers for `SafeInt` and `SafeDec` literals.
pub mod parsing;

/// Re-export of the fixed-precision decimal type.
pub use decimal::SafeDec;
/// Re-export of the arbitrary-precision integer type.
pub use integer::SafeInt;
