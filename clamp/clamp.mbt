///|
pub fn clamp(
  x : Int,
  lo : Int,
  hi : Int,
) -> Int where {
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
