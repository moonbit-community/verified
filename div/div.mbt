///|
pub fn div(
  a : Int,
  b : Int,
) -> Int where {
  proof_require: valid_div_args(a, b),
  proof_ensure: result => div_ok(a, b, result),
} {
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
    proof_invariant: 0 <= lo,
    proof_invariant: lo < hi,
    proof_invariant: lo * b <= a,
    proof_invariant: a < hi * b,
  }
}
