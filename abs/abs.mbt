///|
#ensures(abs_ok(x, result))
pub fn abs(x : Int) -> Int {
  if x >= 0 {
    x
  } else {
    -x
  }
}
