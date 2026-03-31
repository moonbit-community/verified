///|
pub fn isqrt(
  n : Int,
) -> Int where {
  proof_require: nonneg(n),
  proof_ensure: result => isqrt_ok(n, result),
} {
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
    proof_invariant: 0 <= lo,
    proof_invariant: lo < hi,
    proof_invariant: lo * lo <= n,
    proof_invariant: n < hi * hi,
  }
}
