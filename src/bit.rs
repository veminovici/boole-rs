use std::{
    fmt::{Debug, Display},
    ops::{BitAnd, BitOr, BitXor, Not},
};

/// Representation of a bit value, such 0 and 1, or false and true.
///
/// # Examples
///
/// ```rust
/// use boole_rs::Bit;
///
/// let bit = Bit::from(10);
/// assert_eq!(bit, Bit::One);
/// ```
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Bit {
    Zero = 0,
    One = 1,
}

//
// Formatting
//

impl Debug for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Zero => write!(f, "B0"),
            Self::One => write!(f, "B1"),
        }
    }
}

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Zero => write!(f, "0"),
            Self::One => write!(f, "1"),
        }
    }
}

/// Converts an [`u8`] to [`Bit`].
///
/// # Examples
///
/// ```
/// use boole_rs::Bit;
///
/// let bit: Bit = 1_u8.into();
/// assert_eq!(bit, Bit::One);
/// ```
impl From<u8> for Bit {
    #[inline]
    fn from(value: u8) -> Self {
        if value == 0 {
            Bit::Zero
        } else {
            Bit::One
        }
    }
}

/// Converts a [`Bit`] to [`u8`].
///
/// # Examples
///
/// ```
/// use boole_rs::Bit;
///
/// let it: u8 = Bit::One.into();
/// assert_eq!(1, it);
/// ```
impl From<Bit> for u8 {
    #[inline]
    fn from(bit: Bit) -> Self {
        match bit {
            Bit::Zero => 0,
            Bit::One => 1,
        }
    }
}

/// Converts an [`bool`] to [`Bit`].
///
/// # Examples
///
/// ```
/// use boole_rs::Bit;
///
/// let bit: Bit = true.into();
/// assert_eq!(bit, Bit::One);
/// ```
impl From<bool> for Bit {
    #[inline]
    fn from(b: bool) -> Self {
        if b {
            Bit::One
        } else {
            Bit::Zero
        }
    }
}

/// Converts a [`Bit`] to [`bool`].
///
/// # Examples
///
/// ```
/// use boole_rs::Bit;
///
/// let it: bool = Bit::One.into();
/// assert_eq!(true, it);
/// ```
impl From<Bit> for bool {
    fn from(bit: Bit) -> Self {
        match bit {
            Bit::Zero => false,
            Bit::One => true,
        }
    }
}

//
// Logical operations
//

/// Support for AND bitwise operation for [`Bit`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One & Bit::Zero;
/// assert_eq!(Bit::Zero, it);
/// ```
impl BitAnd<Bit> for Bit {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Bit) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs.into();
        (x & y).into()
    }
}

/// Support for AND bitwise for [`Bit`] and [`u8`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One & 0_u8;
/// assert_eq!(Bit::Zero, it);
/// ```
impl BitAnd<u8> for Bit {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: u8) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs > 0;
        (x & y).into()
    }
}

/// Support for OR bitwise for [`Bit`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One | Bit::Zero;
/// assert_eq!(Bit::One, it);
/// ```
impl BitOr<Bit> for Bit {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Bit) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs.into();
        (x | y).into()
    }
}

/// Support for OR bitwise for [`Bit`] and [`u8`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One | 0_u8;
/// assert_eq!(Bit::One, it);
/// ```
impl BitOr<u8> for Bit {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: u8) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs > 0;
        (x | y).into()
    }
}

/// Support for XOR bitwise for [`Bit`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One | Bit::Zero;
/// assert_eq!(Bit::One, it);
/// ```
impl BitXor<Bit> for Bit {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: Bit) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs.into();
        (x ^ y).into()
    }
}

/// Support for OR bitwise for [`Bit`] and [`u8`] operands.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = Bit::One | 0_u8;
/// assert_eq!(Bit::One, it);
/// ```
impl BitXor<u8> for Bit {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: u8) -> Self::Output {
        let x: bool = self.into();
        let y: bool = rhs > 0;
        (x ^ y).into()
    }
}

/// Support for NOT operation over [`Bit`] values.
///
/// # Example
///
/// ```
/// use boole_rs::Bit;
///
/// let it = !Bit::One;
/// assert_eq!(Bit::Zero, it);
/// ```
impl Not for Bit {
    type Output = Bit;

    #[inline]
    fn not(self) -> Self::Output {
        let x: bool = self.into();
        (!x).into()
    }
}

//
// Unit tests
//

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn debug_() {
        let s = format!("{:?}", Bit::Zero);
        assert!(!s.is_empty());

        let s = format!("{:?}", Bit::One);
        assert!(!s.is_empty());
    }

    #[test]
    fn display_() {
        let s = format!("{}", Bit::Zero);
        assert!(!s.is_empty());

        let s = format!("{}", Bit::One);
        assert!(!s.is_empty());
    }

    #[test]
    fn eq_() {
        assert_ne!(Bit::Zero, Bit::One)
    }

    #[test]
    fn clone_() {
        let bit = Bit::Zero;
        let bit1 = bit.clone();

        assert_eq!(bit, bit1);
    }

    #[test]
    fn bit_from_u8_() {
        assert_eq!(Bit::One, 10_u8.into());
        assert_eq!(Bit::Zero, 0_u8.into());
    }

    #[test]
    fn bit_into_u8_() {
        assert_eq!(0_u8, Bit::Zero.into());
        assert_eq!(1_u8, Bit::One.into());
    }

    #[test]
    fn bit_from_bool_() {
        assert_eq!(Bit::One, true.into());
        assert_eq!(Bit::Zero, false.into());
    }

    #[test]
    fn bit_into_bool_() {
        assert_eq!(false, Bit::Zero.into());
        assert_eq!(true, Bit::One.into());
    }

    #[test]
    fn bit_or_bit_() {
        let bit = Bit::One | Bit::Zero;
        assert_eq!(bit, Bit::One);

        let bit = Bit::Zero | Bit::One;
        assert_eq!(bit, Bit::One);

        let bit = Bit::Zero | Bit::Zero;
        assert_eq!(bit, Bit::Zero);
    }

    #[test]
    fn bit_or_u8_() {
        let bit = Bit::One | 0_u8;
        assert_eq!(bit, Bit::One);

        let bit = Bit::Zero | 1_u8;
        assert_eq!(bit, Bit::One);

        let bit = Bit::Zero | 0_u8;
        assert_eq!(bit, Bit::Zero);
    }

    #[test]
    fn bit_and_bit_() {
        let bit = Bit::Zero & Bit::One;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::One & Bit::Zero;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::One & Bit::One;
        assert_eq!(bit, Bit::One);
    }

    #[test]
    fn bit_and_u8_() {
        let bit = Bit::Zero & 1_u8;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::One & 0_u8;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::One & 1_u8;
        assert_eq!(bit, Bit::One);
    }

    #[test]
    fn bit_not() {
        let bit = Bit::Zero;
        assert_eq!(!bit, Bit::One);

        let bit = Bit::One;
        assert_eq!(!bit, Bit::Zero);
    }

    #[test]
    fn bit_xor_bit() {
        let bit = Bit::Zero ^ Bit::Zero;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::Zero ^ Bit::One;
        assert_eq!(bit, Bit::One);

        let bit = Bit::One ^ Bit::Zero;
        assert_eq!(bit, Bit::One);

        let bit = Bit::One ^ Bit::One;
        assert_eq!(bit, Bit::Zero);
    }

    #[test]
    fn bit_xor_u8() {
        let bit = Bit::Zero ^ 0_u8;
        assert_eq!(bit, Bit::Zero);

        let bit = Bit::Zero ^ 1_u8;
        assert_eq!(bit, Bit::One);

        let bit = Bit::One ^ 0_u8;
        assert_eq!(bit, Bit::One);

        let bit = Bit::One ^ 1_u8;
        assert_eq!(bit, Bit::Zero);
    }
}

//
// Property based tests
//

#[cfg(test)]
mod prop_tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    impl quickcheck::Arbitrary for Bit {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            u8::arbitrary(g).into()
        }
    }

    #[quickcheck]
    fn bit_into_from_u8(bit: Bit) -> bool {
        let x: u8 = bit.into();
        let it: Bit = x.into();
        bit == it
    }

    #[quickcheck]
    fn bit_into_from_bool(bit: Bit) -> bool {
        let b: bool = bit.into();
        let it: Bit = b.into();
        bit == it
    }

    #[quickcheck]
    fn bit_not(bit: Bit) -> bool {
        let it: bool = bit.into();
        !bit == (!it).into()
    }

    #[quickcheck]
    fn bit_and_zero(bit: Bit) -> bool {
        let it = bit & Bit::Zero;
        it == Bit::Zero
    }

    #[quickcheck]
    fn bit_and_one(bit: Bit) -> bool {
        let it = bit & Bit::One;
        it == bit
    }

    #[quickcheck]
    fn bit_or_zero(bit: Bit) -> bool {
        let it = bit | Bit::Zero;
        it == bit
    }

    #[quickcheck]
    fn bit_or_one(bit: Bit) -> bool {
        let it = bit | Bit::One;
        it == Bit::One
    }

    #[quickcheck]
    fn bit_xor_zero(bit: Bit) -> bool {
        let it = bit ^ Bit::Zero;
        bit == it
    }

    #[quickcheck]
    fn bit_xor_one(bit: Bit) -> bool {
        let it = bit ^ Bit::One;
        bit == !it
    }
}
