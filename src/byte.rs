use std::{
    fmt::{Binary, Debug, Display, LowerHex, UpperHex},
    ops::{BitAnd, BitOr, BitXor, Shl, Shr},
};

use crate::{Bit, U8_BITS};

const MASKS_SET: [u8; 8] = [128, 64, 32, 16, 8, 4, 2, 1];
const MASKS_RESET: [u8; 8] = [
    !(1 << 7),
    !(1 << 6),
    !(1 << 5),
    !(1 << 4),
    !(1 << 3),
    !(1 << 2),
    !(1 << 1),
    !1,
];

/// Representation of byte where we can access each bit individually.
/// The bits are counted inside of a byte as:
/// 0 1 2 3 | 4 5 6 7
/// 0 0 0 1 | 0 0 1 0
/// So the 3rd and 6th bits are set in the number above.
///
/// # Examples
///
/// ```
/// use boole_rs::{Bit, Byte};
///
/// let byte = Byte::from(10);
///
/// let bit = byte.get_bit(4);
/// assert_eq!(bit, 1.into());
///
/// let mut iter = byte.iter();
/// assert_eq!(iter.next(), Some(Bit::Zero));
/// ```
#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct Byte(u8);

//
// Formatting
//

impl Display for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Debug for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}:{:08b})", self.0, self.0)
    }
}

impl LowerHex for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08x}", self.0)
    }
}

impl UpperHex for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08X}", self.0)
    }
}

impl Binary for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08b}", self.0)
    }
}

//
// Conversion operations
//

/// Converts the [`Byte`] value to a reference of [`u8`].
///
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let byte = Byte::from(10_u8);
/// let it = byte.as_ref();
/// assert_eq!(&10, it);
/// ```
impl AsRef<u8> for Byte {
    fn as_ref(&self) -> &u8 {
        &self.0
    }
}

/// Create a [`Byte`] value from an [`u8`] value.
///
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let byte: Byte = 10_u8.into();
/// let it: u8 = byte.into();
/// assert_eq!(10, it);
/// ```
impl From<u8> for Byte {
    #[inline]
    fn from(value: u8) -> Self {
        Byte(value)
    }
}

/// Create a [`Byte`] value from a &[`u8`] value.
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let byte = Byte::from(&10_u8);
/// let it: u8 = byte.into();
/// assert_eq!(10, it);
/// ```
impl From<&u8> for Byte {
    fn from(value: &u8) -> Self {
        Byte(*value)
    }
}

/// Create an [`u8`] value from a [`Byte`] value.
///
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let byte: Byte = 10_u8.into();
/// let it: u8 = byte.into();
/// assert_eq!(10, it);
/// ```
impl From<Byte> for u8 {
    #[inline]
    fn from(byte: Byte) -> Self {
        byte.0
    }
}

/// Create a [`Byte`] value from a collection of [`Bit`] values.
/// The collection must have at most 8 elements.
///
/// # Examples
///
/// ```
/// use boole_rs::{Bit, Byte};
///
/// let xs = [Bit::Zero, Bit::Zero, Bit::Zero, Bit::Zero, Bit::One, Bit::Zero, Bit::One, Bit::Zero];
/// let byte = Byte::from_iter(xs);
/// assert_eq!(byte, 10_u8.into());
/// ```
impl FromIterator<Bit> for Byte {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Bit>>(iter: T) -> Self {
        iter.into_iter()
            .enumerate()
            .fold(0.into(), |acc, (bit, item)| {
                let idx = bit as u8;
                debug_assert!(idx < U8_BITS as u8);

                if item == Bit::One {
                    acc.set_bit(idx)
                } else {
                    acc
                }
            })
    }
}

/// Create a [`Byte`] value from a collection of [`bool`] values.
/// The collection must have at most 8 elements.
///
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let xs = [0, 0, 0, 0, 1, 0, 1, 0];
/// let byte = Byte::from_iter(xs);
/// assert_eq!(byte, 10_u8.into());
/// ```
impl FromIterator<bool> for Byte {
    #[inline]
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        Byte::from_iter(iter.into_iter().map(|b| Bit::from(b)))
    }
}

/// Create a [`Byte`] value from a collection of [`u8`] values.
/// The collection must have at most 8 elements.
///
/// # Examples
///
/// ```
/// use boole_rs::Byte;
///
/// let xs = [0_u8, 0, 0, 0, 1, 0, 1, 0];
/// let byte = Byte::from_iter(xs);
/// assert_eq!(byte, 10_u8.into());
/// ```
impl FromIterator<u8> for Byte {
    #[inline]
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Byte::from_iter(iter.into_iter().map(|x| Bit::from(x)))
    }
}

//
// Functionality
//

impl Byte {
    /// Returns true if the [`Byte`] value stored is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use boole_rs::Byte;
    ///
    /// let byte = Byte::from(10);
    /// assert!(!byte.is_zero());
    /// ```
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    /// Returns true if the [`Byte`] value stored in one.
    ///
    /// # Examples
    ///
    /// ```
    /// use boole_rs::Byte;
    ///
    /// let byte = Byte::from(1);
    /// assert!(byte.is_one());
    /// ```
    #[inline]
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }

    /// Returns the bit from a [`Byte`] value on a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use boole_rs::{Bit, Byte};
    ///
    /// let byte = Byte::from(10); // 0000 | 1010
    /// assert_eq!(Bit::One, byte.get_bit(4));
    /// assert_eq!(Bit::Zero, byte.get_bit(5));
    /// assert_eq!(Bit::One, byte.get_bit(6));
    /// ```
    #[inline]
    pub fn get_bit(&self, bit: u8) -> Bit {
        let mask = MASKS_SET[bit as usize];
        (self.0 & mask).into()
    }

    /// Sets to one the bit from a [`Byte`] value on a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use boole_rs::{Bit, Byte};
    ///
    /// let byte = Byte::from(10); // 0000 1010
    /// let it = byte.set_bit(5);  // 0000 1110
    /// assert_eq!(it, Byte::from(14));
    /// ```
    #[inline]
    pub fn set_bit(self, bit: u8) -> Self {
        let mask = MASKS_SET[bit as usize];
        Self(self.0 | mask)
    }

    /// Resets to zero the bit from a [`Byte`] value on a given position.
    ///
    /// # Example
    ///
    /// ```
    /// use boole_rs::{Bit, Byte};
    ///
    /// let byte = Byte::from(10);   // 0000 1010
    /// let it = byte.reset_bit(4);  // 0000 0010
    /// assert_eq!(it, Byte::from(2));
    /// ```
    #[inline]
    pub fn reset_bit(self, bit: u8) -> Self {
        let mask = MASKS_RESET[bit as usize];
        Self(self.0 & mask)
    }

    /// Toggles the value of a bit from a [`Byte`] value on a given position.
    ///
    /// # Example
    ///
    /// ```
    /// use boole_rs::{Bit, Byte};
    ///
    /// let byte = Byte::from(10);   // 0000 1010
    /// let it = byte.toggle_bit(4); // 0000 0010
    /// let it = it.toggle_bit(5);   // 0000 0110
    /// assert_eq!(it, Byte::from(6));
    /// ```
    #[inline]
    pub fn toggle_bit(self, bit: u8) -> Self {
        let mask = MASKS_SET[bit as usize];
        Self(self.0 ^ mask)
    }

    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use boole_rs::{Bit, Byte};
    ///
    /// let a = Byte::from(10);
    /// let b = Byte::from(14);
    /// let it = a.is_subset(&b);
    /// assert!(it);
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool {
        for i in 0..U8_BITS {
            let a: bool = self.get_bit(i as u8).into();
            let b: bool = other.get_bit(i as u8).into();
            if a && (a != b) {
                return false;
            }
        }

        true
    }

    /// Returns an iterator which gives access
    /// to every single bit in the [`Byte`] value.
    /// 
    /// # Example
    /// 
    /// ```
    /// use boole_rs::{Bit, Byte};
    /// 
    /// let byte = Byte::from(10);
    /// let mut iter = byte.iter();
    /// 
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// 
    /// assert_eq!(iter.next(), Some(Bit::One));
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// assert_eq!(iter.next(), Some(Bit::One));
    /// assert_eq!(iter.next(), Some(Bit::Zero));
    /// 
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter {
        Iter {
            byte: self.clone(),
            crnt: 0,
        }
    }
}

//
// Byte wise operations
//

impl BitAnd<u8> for Byte {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: u8) -> Self::Output {
        Self(self.0 & rhs)
    }
}

impl BitAnd<Self> for Byte {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        self & rhs.0
    }
}

impl BitOr<u8> for Byte {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: u8) -> Self::Output {
        Self(self.0 | rhs)
    }
}

impl BitOr<Self> for Byte {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        self | rhs.0
    }
}

impl BitXor<u8> for Byte {
    type Output = Self;

    fn bitxor(self, rhs: u8) -> Self::Output {
        Self(self.0 ^ rhs)
    }
}

impl BitXor<Self> for Byte {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self ^ rhs.0
    }
}

impl Shr<u8> for Byte {
    type Output = Self;

    fn shr(self, rhs: u8) -> Self::Output {
        Self(self.0 >> rhs)
    }
}

impl Shl<u8> for Byte {
    type Output = Self;

    fn shl(self, rhs: u8) -> Self::Output {
        Self(self.0 << rhs)
    }
}

//
// Iterator
//

impl IntoIterator for Byte {
    type Item = Bit;

    type IntoIter = Iter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            byte: self,
            crnt: 0,
        }
    }
}

/// Represents an iterator over a byte.
/// The elements of the iteration are [`Bit`] instances.
pub struct Iter {
    byte: Byte,
    crnt: u8,
}

impl Iterator for Iter {
    type Item = Bit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.crnt > 7 {
            None
        } else {
            let res = self.byte.get_bit(self.crnt);
            self.crnt += 1;
            Some(res)
        }
    }
}

//
// Unit tests
//

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn clone_() {
        let x = Byte(10);
        let y = x.clone();
        assert_eq!(x, y)
    }

    #[test]
    fn partial_ord_() {
        let x = Byte(10);
        let y = Byte(11);
        assert!(x < y);
        assert!(y > x);
    }

    #[test]
    fn ord_() {
        let it = Byte(10).max(Byte(1));
        assert_eq!(it, Byte(10));

        let it = Byte(10).min(Byte(1));
        assert_eq!(it, Byte(1));
    }

    #[test]
    fn eq_() {
        let x = Byte(10);
        let y = Byte(10);

        assert_eq!(x, y)
    }

    #[test]
    fn debug_() {
        let s = format!("{:?}", Byte(10));
        assert!(!s.is_empty())
    }

    #[test]
    fn display_() {
        let s = format!("{}", Byte(10));
        assert!(!s.is_empty())
    }

    #[test]
    fn upper_hex_() {
        let s = format!("{:X}", Byte(10));
        assert!(!s.is_empty())
    }

    #[test]
    fn lower_hex_() {
        let s = format!("{:x}", Byte(10));
        assert!(!s.is_empty())
    }

    #[test]
    fn binary_hex_() {
        let s = format!("{:b}", Byte(10));
        assert!(!s.is_empty())
    }

    #[test]
    fn as_ref_() {
        let byte = Byte(10);
        let it = byte.as_ref();
        assert_eq!(&10, it);
    }

    #[test]
    fn byte_from_u8_() {
        let it = Byte::from(10_u8);
        assert_eq!(it.0, 10);
    }

    #[test]
    fn byte_from_ref_u8_() {
        let it = Byte::from(&10_u8);
        assert_eq!(it.0, 10);
    }

    #[test]
    fn byte_into_u8_() {
        let it = Byte::from(10_u8);
        assert_eq!(10_u8, it.into());
    }

    #[test]
    fn byte_from_bits_() {
        let xs = [
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::One,
            Bit::Zero,
            Bit::One,
            Bit::Zero,
        ];
        let byte = Byte::from_iter(xs);
        assert_eq!(byte, 10_u8.into());
    }

    #[test]
    fn byte_from_bools_() {
        let xs = [false, false, false, false, true, false, true, false];
        let byte = Byte::from_iter(xs);
        assert_eq!(byte, 10_u8.into());
    }

    #[test]
    fn byte_from_bytes_() {
        let xs = [0_u8, 0, 0, 0, 1, 0, 1, 0];
        let byte = Byte::from_iter(xs);
        assert_eq!(byte, 10_u8.into());
    }

    #[test]
    fn is_zero_() {
        assert!(Byte::from(0).is_zero());
        assert!(!Byte::from(10).is_zero());
    }

    #[test]
    fn is_one_() {
        assert!(Byte::from(1).is_one());
        assert!(!Byte::from(10).is_one());
    }

    #[test]
    fn get_bit_() {
        let byte = Byte::from(10);
        assert_eq!(byte.get_bit(0), Bit::Zero);
        assert_eq!(byte.get_bit(4), Bit::One);
    }

    #[test]
    fn set_bit_() {
        let byte = Byte::from(10);
        let byte = byte.set_bit(7);
        assert_eq!(byte, 11.into());
    }

    #[test]
    fn reset_bit_() {
        let byte = Byte::from(10);
        let byte = byte.reset_bit(6);
        assert_eq!(byte, 8.into());
    }

    #[test]
    fn toggle_bit_() {
        let byte = Byte::from(10);
        let byte = byte.toggle_bit(6);
        assert_eq!(byte, 8.into());
    }

    #[test]
    fn and_u8_() {
        let byte = Byte::from(10);
        let it = byte & 2;
        assert_eq!(it, 2.into());
    }

    #[test]
    fn and_byte_() {
        let byte = Byte::from(10);
        let it = byte & Byte::from(2);
        assert_eq!(it, 2.into());
    }

    #[test]
    fn or_u8_() {
        let byte = Byte::from(8);
        let it = byte | 2;
        assert_eq!(it, 10.into());
    }

    #[test]
    fn or_byte_() {
        let byte = Byte::from(8);
        let it = byte | Byte::from(2);
        assert_eq!(it, 10.into());
    }

    #[test]
    fn xor_u8_() {
        let byte = Byte::from(2);
        let it = byte ^ 3;
        assert_eq!(it, 1.into());
    }

    #[test]
    fn xor_byte_() {
        let byte = Byte::from(2);
        let it = byte ^ Byte::from(3);
        assert_eq!(it, 1.into());
    }

    #[test]
    fn shr_() {
        let byte = Byte::from(10);
        let it = byte >> 1;
        assert_eq!(it, 5.into());
    }

    #[test]
    fn shl_() {
        let byte = Byte::from(5);
        let it = byte << 1;
        assert_eq!(it, 10.into());
    }

    #[test]
    fn byte_iter_() {
        let byte = Byte::from(10);
        let mut iter = byte.iter();

        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));

        assert_eq!(iter.next(), Some(Bit::One));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::One));
        assert_eq!(iter.next(), Some(Bit::Zero));

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn byte_into_iter_() {
        let byte = Byte::from(10);
        let mut iter = byte.into_iter();

        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::Zero));

        assert_eq!(iter.next(), Some(Bit::One));
        assert_eq!(iter.next(), Some(Bit::Zero));
        assert_eq!(iter.next(), Some(Bit::One));
        assert_eq!(iter.next(), Some(Bit::Zero));

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn is_subset_() {
        let a = Byte::from(10);
        let b = Byte::from(14);
        let it = a.is_subset(&b);
        assert!(it);

        let it = b.is_subset(&a);
        assert!(!it);
    }
}

#[cfg(test)]
mod prop_tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    /// Random values for Byte
    impl quickcheck::Arbitrary for Byte {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            u8::arbitrary(g).into()
        }
    }

    /// Argument for building the Byte from a list of u8 elements.
    #[derive(Clone, Copy, Debug)]
    pub struct Bytes {
        pub xs: [u8; 8],
    }

    impl quickcheck::Arbitrary for Bytes {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let u0 = u8::arbitrary(g) % 2;
            let u1 = u8::arbitrary(g) % 2;
            let u2 = u8::arbitrary(g) % 2;
            let u3 = u8::arbitrary(g) % 2;
            let u4 = u8::arbitrary(g) % 2;
            let u5 = u8::arbitrary(g) % 2;
            let u6 = u8::arbitrary(g) % 2;
            let u7 = u8::arbitrary(g) % 2;

            let xs = [u0, u1, u2, u3, u4, u5, u6, u7];
            Bytes { xs }
        }
    }

    /// Arguments for building the Byte for a list of bool elements.
    #[derive(Clone, Copy, Debug)]
    pub struct Bools {
        pub xs: [bool; 8],
    }

    impl quickcheck::Arbitrary for Bools {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let u0 = u8::arbitrary(g) % 2;
            let u1 = u8::arbitrary(g) % 2;
            let u2 = u8::arbitrary(g) % 2;
            let u3 = u8::arbitrary(g) % 2;
            let u4 = u8::arbitrary(g) % 2;
            let u5 = u8::arbitrary(g) % 2;
            let u6 = u8::arbitrary(g) % 2;
            let u7 = u8::arbitrary(g) % 2;

            let xs = [u0, u1, u2, u3, u4, u5, u6, u7].map(|u| if u == 0 { false } else { true });
            Bools { xs }
        }
    }

    #[quickcheck]
    fn u8_from_into_byte(x: u8) -> bool {
        let byte = Byte::from(x);
        x == byte.into()
    }

    #[quickcheck]
    fn display_(byte: Byte) -> bool {
        !format!("byte: {byte}").is_empty()
    }

    #[quickcheck]
    fn byte_set(byte: Byte, bit: u8) -> bool {
        let bit = bit % 8;
        let byte = byte.set_bit(bit);
        Bit::One == byte.get_bit(bit)
    }

    #[quickcheck]
    fn byte_reset(byte: Byte, bit: u8) -> bool {
        let bit = bit % 8;
        let byte = byte.reset_bit(bit);
        Bit::Zero == byte.get_bit(bit)
    }

    #[quickcheck]
    fn byte_toggle(byte: Byte, bit: u8) -> bool {
        let bit = bit % 8;

        let orig = byte.get_bit(bit);
        let byte = byte.toggle_bit(bit);
        let upd = byte.get_bit(bit);

        orig != upd
    }

    #[quickcheck]
    fn eq_(byte: Byte) -> bool {
        let byte1 = byte.clone();
        byte1 == byte
    }

    #[quickcheck]
    fn diff_(byte: Byte, bit: u8) -> bool {
        let bit = bit % 8;
        let byte1 = byte.toggle_bit(bit);
        byte1 != byte
    }

    #[quickcheck]
    fn ord_(byte: Byte, bit: u8) -> bool {
        let bit = bit % 8;
        let byte1 = byte.set_bit(bit);
        byte <= byte1
    }

    #[quickcheck]
    fn from_bytes(bytes: Bytes) -> bool {
        let xs = bytes.clone();
        let _s = format!("{:?}", xs);

        let byte = Byte::from_iter(bytes.xs);
        let iter = byte.iter().map(|b| u8::from(b));
        iter.zip(bytes.xs).all(|(i, x)| i == x)
    }

    #[quickcheck]
    fn from_bools(bools: Bools) -> bool {
        let xs = bools.clone();
        let _s = format!("{:?}", xs);

        let byte = Byte::from_iter(bools.xs);
        let iter = bools.xs.map(|b| if b { Bit::One } else { Bit::Zero });
        byte.iter().zip(iter).all(|(i, j)| i == j)
    }
}
