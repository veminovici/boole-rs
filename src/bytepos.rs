use std::{
    fmt::{Debug, Display},
    ops::{Add, Sub},
};

use crate::U8_BITS;

/// Represents a position of a [`Bit`] inside a vector of [`Byte`] values.
#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub(crate) struct BytePos {
    pub(crate) idx: usize,
    pub(crate) bit: u8,
}

//
// Formatting
//

impl Display for BytePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pos: usize = (*self).into();
        write!(f, "{pos}")
    }
}

impl Debug for BytePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}:{})", self.idx, self.bit)
    }
}

//
// Convertion operations
//

impl From<usize> for BytePos {
    #[inline]
    fn from(idx: usize) -> Self {
        Self {
            idx: idx / U8_BITS,
            bit: (idx % U8_BITS) as u8,
        }
    }
}

impl From<BytePos> for usize {
    #[inline]
    fn from(pos: BytePos) -> Self {
        pos.idx * U8_BITS + pos.bit as usize
    }
}

//
// Add and Sub operations
//

impl Add<usize> for BytePos {
    type Output = Self;

    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        let x: usize = self.into();
        (x + rhs).into()
    }
}

impl Sub<usize> for BytePos {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        let x: usize = self.into();
        debug_assert!(x >= rhs);
        (x - rhs).into()
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn display_() {
        let pos: BytePos = 10_usize.into();
        println!("byte_pos: {pos}");
    }

    #[test]
    fn debug_() {
        let pos: BytePos = 10_usize.into();
        println!("byte_pos: {pos:?}");
    }

    #[test]
    fn idx_bit() {
        let x: BytePos = 10_usize.into();
        assert_eq!(1, x.idx);
        assert_eq!(2, x.bit);
    }

    #[test]
    fn eq_() {
        let x: BytePos = 10_usize.into();
        let y: BytePos = 10_usize.into();
        assert!(x == y)
    }

    #[test]
    fn cmp_() {
        let x: BytePos = 10_usize.into();
        let y: BytePos = 11_usize.into();
        assert!(x < y);
        assert!(y > x);
    }

    #[test]
    fn ord_() {
        let x: BytePos = 10_usize.into();
        let y: BytePos = 11_usize.into();

        let it = x.max(y);
        assert_eq!(it, y);

        let it = x.min(y);
        assert_eq!(it, x);
    }

    #[test]
    fn clone_() {
        let x: BytePos = 10_usize.into();
        let y: BytePos = x.clone();
        assert!(x == y)
    }

    #[test]
    fn copy_() {
        let x: BytePos = 10_usize.into();
        let y: BytePos = x;
        assert!(y == 10.into())
    }

    #[test]
    fn add_() {
        let x: BytePos = 10_usize.into();
        let y = x + 1;
        assert!(y == 11.into())
    }

    #[test]
    fn sub_() {
        let x: BytePos = 10_usize.into();
        let y = x - 1;
        assert!(y == 9.into())
    }
}

#[cfg(test)]
mod prop_tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    /// Random values for BytePos
    impl quickcheck::Arbitrary for BytePos {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let it = usize::arbitrary(g);
            BytePos::from(it)
        }
    }

    #[quickcheck]
    fn display_(pos: BytePos) -> bool {
        eprintln!("byte_pos: {pos}");
        true
    }

    #[quickcheck]
    fn debug_(pos: BytePos) -> bool {
        eprintln!("byte_pos: {pos:?}");
        true
    }

    #[quickcheck]
    fn add_(x: usize) -> bool {
        let x = x / 10 ^ 4;
        let pos = BytePos::from(x);
        let pos1 = pos + 1;
        pos < pos1
    }

    #[quickcheck]
    fn sub_(x: usize) -> bool {
        let x = x / 10 ^ 4;
        let pos = BytePos::from(x);
        let pos1 = pos - 1;
        pos1 < pos
    }

    #[quickcheck]
    fn eq_(x: usize) -> bool {
        let x = x / 10 ^ 4;
        let pos = BytePos::from(x);
        let pos1 = pos + 0;
        pos == pos1
    }
}
