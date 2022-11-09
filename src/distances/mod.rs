//! Distances
//! 
//! $$
//! f(x) = \int_{-\infty}^\infty
//!   \hat f(\xi)e^{2 \pi i \xi x}
//!   d\xi
//! $$

use num_traits::{Num, NumAssign, Signed};

/// Value representing a distance
pub trait Value: Copy + Num + NumAssign + Signed + PartialOrd {}

/// All numeric values can be distance values. It is a blanket [`Value`] implementation.
impl<T: Copy + Num + NumAssign + Signed + PartialOrd> Value for T {}

/// A distance between two points.
/// A distance can be copied, converted into the inner value,
/// compared with another distance or distance value.
pub trait Distance
where
    Self: Copy,
    Self: Into<<Self as Distance>::Value>,
    Self: PartialOrd<<Self as Distance>::Value>,
    Self: PartialOrd,
{
    /// The type of the distance
    type Value: Value + PartialOrd<Self>;

    /// Get the distance value.
    fn value(self) -> Self::Value {
        self.into()
    }
}

/// Any distance value implements distance.
impl<T: Value> Distance for T {
    type Value = T;
}