///|
#requires(valid_bounds(lo, hi))
#ensures(clamped(lo, hi, result))
pub fn clamp(x : Int, lo : Int, hi : Int) -> Int {
  if x < lo {
    lo
  } else if x > hi {
    hi
  } else {
    x
  }
}
