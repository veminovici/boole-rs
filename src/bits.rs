use std::fmt::{Debug, LowerHex, UpperHex};

use crate::{Bit, Byte, BytePos};

pub struct Bits {
    inner: Vec<u8>,
    len: usize,
}

//
// Formatting
//

impl Debug for Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bits ({}): ", self.len)?;

        let mut with_separator = false;
        for x in &self.inner {
            if with_separator {
                write!(f, "|{:08b}", x).unwrap();
            } else {
                write!(f, "{:08b}", x).unwrap();
                with_separator = true;
            }
        }

        std::fmt::Result::Ok(())
    }
}

impl UpperHex for Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bits ({}): ", self.len)?;

        let mut with_separator = false;
        for x in &self.inner {
            if with_separator {
                write!(f, "|{:02X}", x).unwrap();
            } else {
                write!(f, "{:02X}", x).unwrap();
                with_separator = true;
            }
        }

        std::fmt::Result::Ok(())
    }
}

impl LowerHex for Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bits ({}): ", self.len)?;

        let mut with_separator = false;
        for x in &self.inner {
            if with_separator {
                write!(f, "|{:02x}", x).unwrap();
            } else {
                write!(f, "{:02x}", x).unwrap();
                with_separator = true;
            }
        }

        std::fmt::Result::Ok(())
    }
}

//
// Functionality
//

fn get_capacity(len: usize) -> usize {
    let pos = BytePos::from(len);
    let mut capacity = pos.idx;
    if pos.bit != 0 {
        capacity += 1;
    }

    capacity
}

impl Bits {
    pub fn with_length(len: usize) -> Self {
        let capacity = get_capacity(len);
        let mut inner = Vec::with_capacity(capacity);
        let _x: usize = (0..capacity).inspect(|_| inner.push(0)).sum();

        Bits { inner, len }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn get_bit(&self, index: usize) -> Bit {
        debug_assert!(index < self.len);

        let pos = BytePos::from(index);
        let byte: Byte = self.inner[pos.idx].into();
        byte.get_bit(pos.bit)
    }

    pub fn set_bit(&mut self, index: usize) {
        debug_assert!(index < self.len);

        let pos = BytePos::from(index);
        let byte: Byte = self.inner[pos.idx].into();
        self.inner[pos.idx] = byte.set_bit(pos.bit).into();
    }

    pub fn reset_bit(&mut self, index: usize) {
        debug_assert!(index < self.len);

        let pos = BytePos::from(index);
        let byte: Byte = self.inner[pos.idx].into();
        self.inner[pos.idx] = byte.reset_bit(pos.bit).into();
    }

    pub fn toggle_bit(&mut self, index: usize) {
        debug_assert!(index < self.len);

        let pos = BytePos::from(index);
        let byte: Byte = self.inner[pos.idx].into();
        self.inner[pos.idx] = byte.toggle_bit(pos.bit).into();
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }

        for idx in 0..self.inner.len() {
            let x: Byte = self.inner[idx].into();
            let y: Byte = other.inner[idx].into();

            if !x.is_subset(&y) {
                return false;
            }
        }

        true
    }
}

//
// Conversion functions
//

impl<const N: usize> From<[bool; N]> for Bits {
    fn from(bs: [bool; N]) -> Self {
        let mut bits = Bits::with_length(N);
        let _xs: Vec<()> = bs
            .iter()
            .enumerate()
            .inspect(|(i, b)| {
                if **b {
                    bits.set_bit(*i);
                }
            })
            .map(|_| ())
            .collect();

        bits
    }
}

impl<const N: usize> From<[Bit; N]> for Bits {
    fn from(bs: [Bit; N]) -> Self {
        let mut bits = Bits::with_length(N);
        let _xs: Vec<()> = bs
            .iter()
            .enumerate()
            .inspect(|(i, b)| {
                if **b == Bit::One {
                    bits.set_bit(*i);
                }
            })
            .map(|_| ())
            .collect();

        bits
    }
}

impl<const N: usize> From<[u8; N]> for Bits {
    fn from(bs: [u8; N]) -> Self {
        let mut bits = Bits::with_length(N);
        let _xs: Vec<()> = bs
            .iter()
            .enumerate()
            .inspect(|(i, b)| {
                if **b != 0 {
                    bits.set_bit(*i);
                }
            })
            .map(|_| ())
            .collect();

        bits
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn format_() {
        let bits = Bits {
            inner: vec![1, 0xA2],
            len: 8,
        };

        eprintln!("BITS (b): {bits:?}");
        eprintln!("BITS (X): {bits:X}");
        eprintln!("BITS (x): {bits:x}");
    }

    #[test]
    fn with_length_() {
        let bits = Bits::with_length(8);
        assert_eq!(bits.inner.len(), 1);

        let bits = Bits::with_length(12);
        assert_eq!(bits.inner.len(), 2);
    }

    #[test]
    fn len_() {
        let bits = Bits::with_length(8);
        assert_eq!(bits.inner.len(), 1);
        assert_eq!(bits.len(), 8);

        let bits = Bits::with_length(12);
        assert_eq!(bits.inner.len(), 2);
        assert_eq!(bits.len(), 12);
    }

    #[test]
    fn is_empty() {
        let bits = Bits::with_length(8);
        assert_eq!(bits.inner.len(), 1);
        assert!(!bits.is_empty());
    }

    #[test]
    fn set_() {
        let mut bits = Bits::with_length(16);
        bits.set_bit(2);
        bits.set_bit(8);
    }

    #[test]
    fn get_() {
        let mut bits = Bits::with_length(16);
        bits.set_bit(2);
        bits.set_bit(8);

        let it = bits.get_bit(2);
        assert_eq!(it, Bit::One);

        let it = bits.get_bit(3);
        assert_eq!(it, Bit::Zero);

        let it = bits.get_bit(8);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn reset_() {
        let mut bits = Bits::with_length(16);
        bits.set_bit(2);
        bits.set_bit(8);
        bits.reset_bit(2);

        let it = bits.get_bit(2);
        assert_eq!(it, Bit::Zero);

        let it = bits.get_bit(8);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn toggle_bit_() {
        let mut bits = Bits::with_length(16);
        bits.set_bit(2);
        bits.set_bit(8);

        bits.toggle_bit(2);
        let it = bits.get_bit(2);
        assert_eq!(it, Bit::Zero);

        bits.toggle_bit(1);
        let it = bits.get_bit(1);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn from_bools_n_() {
        let bs = [
            false, true, false, false, false, false, false, false, true, false,
        ];
        let bits = Bits::from(bs);

        let it = bits.get_bit(1);
        assert_eq!(it, Bit::One);

        let it = bits.get_bit(3);
        assert_eq!(it, Bit::Zero);

        let it = bits.get_bit(8);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn from_bits_n_() {
        let bs = [
            Bit::Zero,
            Bit::One,
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::Zero,
            Bit::One,
            Bit::Zero,
        ];
        let bits = Bits::from(bs);

        let it = bits.get_bit(1);
        assert_eq!(it, Bit::One);

        let it = bits.get_bit(3);
        assert_eq!(it, Bit::Zero);

        let it = bits.get_bit(8);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn from_bytes_n_() {
        let bs = [0_u8, 1, 0, 0, 0, 0, 0, 0, 1, 0];
        let bits = Bits::from(bs);

        let it = bits.get_bit(1);
        assert_eq!(it, Bit::One);

        let it = bits.get_bit(3);
        assert_eq!(it, Bit::Zero);

        let it = bits.get_bit(8);
        assert_eq!(it, Bit::One);
    }

    #[test]
    fn is_subset_() {
        let xs = Bits {
            inner: vec![0x1, 0xA],
            len: 16,
        };

        let ys = Bits {
            inner: vec![0x5, 0xA],
            len: 16,
        };

        assert!(xs.is_subset(&ys));
    }

    #[test]
    fn is_subset_diff_len_() {
        let xs = Bits {
            inner: vec![0xA],
            len: 8,
        };

        let ys = Bits {
            inner: vec![0x5, 0xA],
            len: 16,
        };

        assert!(!xs.is_subset(&ys));
    }

    #[test]
    fn is_subset_diff_byte() {
        let xs = Bits {
            inner: vec![0x1, 0xA],
            len: 16,
        };

        let ys = Bits {
            inner: vec![0x5, 0xA],
            len: 16,
        };

        assert!(!ys.is_subset(&xs));
    }
}
