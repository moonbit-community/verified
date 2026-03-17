///|
#requires(nonneg(n))
#ensures(isqrt_ok(n, result))
pub fn isqrt(n : Int) -> Int {
  for lo = 0, hi = n + 1; lo < hi - 1; {
    let mid = lo + (hi - lo) / 2
    if mid * mid <= n {
      continue mid, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  } where {
    invariant: 0 <= lo,
    invariant: lo < hi,
    invariant: lo * lo <= n,
    invariant: n < hi * hi,
  }
}
