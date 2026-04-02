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
    proof_reasoning: (
      #| The loop keeps the true integer square root trapped between two
      #| bracketing candidates: `lo` is always feasible because `lo * lo <= n`,
      #| while `hi` is always too large because `n < hi * hi`.
      #|
      #| Initially `lo = 0` and `hi = n + 1`, and for nonnegative `n` we have
      #| `0 <= n < (n + 1) * (n + 1)`.
      #|
      #| At midpoint `mid`, the test `mid * mid <= n` decides which side still
      #| contains the answer:
      #|   - If true, `mid` is a valid lower bound, so we can raise `lo` to `mid`.
      #|   - If false, `mid` is already too large, so we can lower `hi` to `mid`.
      #|
      #| Under the guard `lo < hi - 1`, the midpoint lies strictly inside the
      #| interval, so either update makes the gap `hi - lo` strictly smaller.
      #| The loop stops exactly when the two bounds become consecutive,
      #| i.e. `hi == lo + 1`.
      #|
      #| At exit the invariants become `lo * lo <= n < hi * hi` together with
      #| `hi == lo + 1`, which is precisely `lo * lo <= n < (lo + 1) * (lo + 1)`.
    ),
  }
}
