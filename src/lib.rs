#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

//! `const@Zero` and `const@One` ZSTs for use with generic code.
//!
//! These can be used in generic code where `0` and `1` literals don't work.
//!
//! ```
//! # #![allow(non_upper_case_globals)]
//! use zero_one::{Zero, One};
//!
//! assert_eq!(u64::from(Zero), 0);
//! assert_eq!(i8::from(Zero), 0);
//! assert_eq!(u64::from(One), 1);
//! assert_eq!(i8::from(One), 1);
//!
//! assert_eq!(Zero, 0);
//! assert_ne!(Zero, 1);
//! assert_ne!(One, 0);
//! assert_eq!(One, 1);
//!
//! assert!(Zero < 10);
//! assert!(-10 < Zero);
//! assert!(One < 10);
//! assert!(-10 < One);
//!
//! assert!(matches!(Zero::try_from(0_u16), Ok(Zero)));
//! assert!(matches!(Zero::try_from(1_i16), Err(_)));
//! assert!(matches!(One::try_from(0_u16), Err(_)));
//! assert!(matches!(One::try_from(1_i16), Ok(One)));
//!
//! assert_eq!(Zero.to_string(), "0");
//! assert_eq!(One.to_string(), "1");
//! ```
//!
//! Even outside generic code, they can make it easier to use some `std` types:
//! ```
//! use zero_one::{Zero, One};
//! use std::num::*;
//!
//! assert_eq!(NonZeroU64::from(One), NonZeroU64::new(1).unwrap());
//! assert_eq!(NonZeroI8::from(One), NonZeroI8::new(1).unwrap());
//! ```
//!
//! They'll even work in macros that want to `as` cast things:
//! ```
//! use zero_one::{Zero, One};
//!
//! assert_eq!(Zero as u32, 0);
//! assert_eq!(Zero as i128, 0);
//! assert_eq!(One as u32, 1);
//! assert_eq!(One as i128, 1);
//! ```
//!
//! You can do math with them, too:
//! ```
//! use zero_one::{Zero, One};
//!
//! assert_eq!(Zero + 5, 5);
//! assert_eq!(Zero | 5, 5);
//! assert_eq!(One * 5, 5);
//! assert_eq!(One + 5, 6);
//!
//! assert_eq!(Zero % One, Zero);
//! assert_eq!(One - Zero, One);
//! assert_eq!(Zero * 5, Zero);
//! assert_eq!(Zero & 5, Zero);
//!
//! assert_eq!(10 + One, 11);
//! assert_eq!(10 + Zero, 10);
//! ```

use core::cmp::{self, Eq, Ord, PartialEq, PartialOrd};
use core::fmt::{self, Display, Formatter};
use core::ops;

/// The additive identity; the smallest natural number.
#[allow(non_upper_case_globals)] // This is aping `struct Zero;`, so *shouldn't* be upper case.
pub const Zero: Zero = Zero::Zero;

/// The type whose only possible value is [`const@Zero`].
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Zero {
    /// Yes, this is an enum.  But please don't mention the variant.
    /// You should always just use [`const@Zero`] instead.
    Zero = 0,
}

impl<T> ops::Add<T> for Zero {
    type Output = T;
    fn add(self, other: T) -> T { other }
}

impl<T> ops::Mul<T> for Zero {
    type Output = Zero;
    fn mul(self, _: T) -> Zero { Zero }
}

impl<T> ops::BitOr<T> for Zero {
    type Output = T;
    fn bitor(self, other: T) -> T { other }
}

impl<T> ops::BitAnd<T> for Zero {
    type Output = Zero;
    fn bitand(self, _: T) -> Zero { Zero }
}

impl Display for Zero {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        <u8 as Display>::fmt(&0, f)
    }
}

/// The multiplicative identity; the distance between adjacent natural numbers.
#[allow(non_upper_case_globals)] // This is aping `struct One;`, so *shouldn't* be upper case.
pub const One: One = One::One;

/// The type whose only possible value is [`const@One`].
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum One {
    /// Yes, this is an enum.  But please don't mention the variant.
    /// You should always just use [`const@One`] instead.
    One = 1,
}

impl<T: ops::Add<One>> ops::Add<T> for One {
    type Output = T::Output;
    fn add(self, other: T) -> Self::Output {
        other + self
    }
}

impl<T> ops::Mul<T> for One {
    type Output = T;
    fn mul(self, other: T) -> T { other }
}

impl Display for One {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        <u8 as Display>::fmt(&1, f)
    }
}

macro_rules! impl_math_identities {
    ($($trait:ident/$method:ident: $lhs:ident $rhs:ident -> $out:ident,)+) => {$(
        impl ops::$trait<$rhs> for $lhs {
            type Output = $out;
            fn $method(self, _: $rhs) -> $out { $out }
        }
    )+};
}

impl_math_identities!{
    // 0 + x -> x is covered by the blanket impl
    // 1 + x -> x + 1
    Sub/sub: Zero Zero -> Zero,
    Sub/sub: One Zero -> One,
    Sub/sub: One One -> Zero,
    // 0 * x -> 0 is covered by the blanket impl
    // 1 * x -> x is covered by the blanket impl
    Div/div: Zero One -> Zero,
    Div/div: One One -> One,
    Rem/rem: Zero One -> Zero,
    Rem/rem: One One -> Zero,

    // 0 & x -> 0 is covered by the blanket impl
    BitAnd/bitand: One Zero -> Zero,
    BitAnd/bitand: One One -> One,
    // 0 | x -> c is covered by the blanket impl
    BitOr/bitor: One Zero -> One,
    BitOr/bitor: One One -> One,
    BitXor/bitxor: Zero Zero -> Zero,
    BitXor/bitxor: Zero One -> One,
    BitXor/bitxor: One Zero -> One,
    BitXor/bitxor: One One -> Zero,
    Shl/shl: Zero Zero -> Zero,
    Shl/shl: Zero One -> Zero,
    Shl/shl: One Zero -> One,
    Shr/shr: Zero Zero -> Zero,
    Shr/shr: One Zero -> One,
    Shr/shr: Zero One -> Zero,
    Shr/shr: One One -> Zero,
}

macro_rules! impl_for_integer {
    ($($t:ty,)+) => {$(
        impl From<Zero> for $t {
            fn from(_: Zero) -> $t { 0 }
        }
        impl From<One> for $t {
            fn from(_: One) -> $t { 1 }
        }

        impl TryFrom<$t> for Zero {
            type Error = core::num::TryFromIntError;
            fn try_from(other: $t) -> Result<Zero, Self::Error> {
                if other == 0 {
                    Ok(Zero)
                } else {
                    u8::try_from(-1).map(|_| unreachable!())
                }
            }
        }
        impl TryFrom<$t> for One {
            type Error = core::num::TryFromIntError;
            fn try_from(other: $t) -> Result<One, Self::Error> {
                if other == 1 {
                    Ok(One)
                } else {
                    u8::try_from(-1).map(|_| unreachable!())
                }
            }
        }

        impl PartialEq<$t> for Zero {
            fn eq(&self, other: &$t) -> bool {
                *other == 0
            }
        }
        impl PartialEq<$t> for One {
            fn eq(&self, other: &$t) -> bool {
                *other == 1
            }
        }

        impl PartialEq<Zero> for $t {
            fn eq(&self, other: &Zero) -> bool {
                *other == *self
            }
        }
        impl PartialEq<One> for $t {
            fn eq(&self, other: &One) -> bool {
                *other == *self
            }
        }

        impl PartialOrd<$t> for Zero {
            fn partial_cmp(&self, other: &$t) -> Option<cmp::Ordering> {
                <$t as PartialOrd>::partial_cmp(&0, other)
            }
        }
        impl PartialOrd<$t> for One {
            fn partial_cmp(&self, other: &$t) -> Option<cmp::Ordering> {
                <$t as PartialOrd>::partial_cmp(&1, other)
            }
        }

        impl PartialOrd<Zero> for $t {
            fn partial_cmp(&self, _other: &Zero) -> Option<cmp::Ordering> {
                <$t as PartialOrd>::partial_cmp(self, &0)
            }
        }
        impl PartialOrd<One> for $t {
            fn partial_cmp(&self, _other: &One) -> Option<cmp::Ordering> {
                <$t as PartialOrd>::partial_cmp(self, &1)
            }
        }

        impl ops::Add<Zero> for $t {
            type Output = $t;
            fn add(self, _: Zero) -> $t {
                self + 0
            }
        }
        impl ops::Add<One> for $t {
            type Output = $t;
            fn add(self, _: One) -> $t {
                self + 1
            }
        }
    )+};
}

impl_for_integer!{
    i8, i16, i32, i64, i128, isize,
    u8, u16, u32, u64, u128, usize,
}

macro_rules! impl_for_nonzero_integer {
    ($($t:ty,)+) => {$(
        #[allow(unused_imports)]
        use core::num::*;

        impl From<One> for $t {
            fn from(_: One) -> $t { <$t>::new(1).unwrap() }
        }

        impl TryFrom<$t> for One {
            type Error = TryFromIntError;
            fn try_from(other: $t) -> Result<One, Self::Error> {
                if other.get() == 1 {
                    Ok(One)
                } else {
                    u8::try_from(-1).map(|_| unreachable!())
                }
            }
        }
    )+};
}

impl_for_nonzero_integer!{
    NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize,
    NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
}

impl ops::Neg for Zero {
    type Output = Zero;
    fn neg(self) -> Zero { Zero }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn some_basics() {
        assert_eq!(std::mem::size_of::<Zero>(), 0);
        assert_eq!(std::mem::size_of::<One>(), 0);

        assert_eq!(Zero as i8, 0);
        assert_eq!(Zero as u128, 0);
        assert_eq!(One as u8, 1);
        assert_eq!(One as i128, 1);

        assert_eq!(Zero + Zero, Zero);
        assert_eq!(One * One, One);
    }
}
