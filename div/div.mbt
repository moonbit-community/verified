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
    proof_reasoning: (
      #| This is the same bracketing pattern as binary search, but over possible
      #| quotients. `lo` is always a feasible quotient because `lo * b <= a`,
      #| while `hi` is always too large because `a < hi * b`.
      #|
      #| With `a >= 0` and `b > 0`, the initial bounds `lo = 0` and `hi = a + 1`
      #| satisfy the invariant.
      #|
      #| At midpoint `mid`, the predicate `mid * b <= a` tells us whether `mid`
      #| is still feasible:
      #|   - If true, the quotient is at least `mid`, so we move `lo` up to `mid`.
      #|   - If false, `mid` is already too large, so we move `hi` down to `mid`.
      #|
      #| The integer width `hi - lo` decreases on every iteration, and the loop
      #| exits when no integer remains strictly between the two bounds.
      #|
      #| Therefore at exit `hi == lo + 1`, and the invariants give
      #| `lo * b <= a < (lo + 1) * b`, which is exactly `div_ok(a, b, lo)`.
    ),
  }
}
