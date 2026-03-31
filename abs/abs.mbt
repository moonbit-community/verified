///|
pub fn abs(x : Int) -> Int where { proof_ensure: result => abs_ok(x, result) } {
  if x >= 0 {
    x
  } else {
    -x
  }
}
