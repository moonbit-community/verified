///|
/// `valid_bounds(lo, hi)` is the only precondition; once it holds, each branch returns a
/// value that already satisfies the clamped-range postcondition.
pub fn clamp(
  x : Int32,
  lo : Int32,
  hi : Int32,
) -> Int32 where {
  proof_require: valid_bounds(lo, hi),
  proof_ensure: result => clamped(lo, hi, result),
} {
  if x < lo {
    lo
  } else if x > hi {
    hi
  } else {
    x
  }
}
