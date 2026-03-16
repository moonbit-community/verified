#requires(valid_div_args(a, b))
#ensures(div_ok(a, b, result))
pub fn div(a : Int, b : Int) -> Int {
  for lo = 0, hi = a + 1; lo < hi - 1; {
    let mid = lo + (hi - lo) / 2
    if mid * b <= a {
      continue mid, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  } where {
    invariant: 0 <= lo,
    invariant: lo < hi,
    invariant: lo * b <= a,
    invariant: a < hi * b,
  }
}
