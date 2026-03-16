#ensures(is_max(a, b, result))
pub fn max(a : Int, b : Int) -> Int {
  if a >= b {
    a
  } else {
    b
  }
}
