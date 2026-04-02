///|
/// The proof splits on the sign of `x`; either branch returns the magnitude that the
/// `abs_ok` postcondition names.
pub fn abs(x : Int) -> Int where { proof_ensure: result => abs_ok(x, result) } {
  if x >= 0 {
    x
  } else {
    -x
  }
}
