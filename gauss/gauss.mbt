///|
pub fn sum_to(
  n : Int,
) -> Int where {
  proof_require: nonneg(n),
  proof_ensure: result => gauss_ok(n, result),
} {
  for i = 0, sum = 0; i < n; {
    let new_sum = sum + i + 1
    continue i + 1, new_sum
  } nobreak {
    sum
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: sum * 2 == i * (i + 1),
    reasoning: (
      #| The invariant states the exact closed form for the prefix sum, not just
      #| a bound: after processing `i` terms we have `2 * sum == i * (i + 1)`.
      #| That gives the proof a single algebraic target to preserve.
      #|
      #| Initialization is immediate at `i = 0`, `sum = 0`.
      #|
      #| On each iteration we add `i + 1`, so the new state satisfies
      #| `2 * new_sum == 2 * sum + 2 * (i + 1)`. Substituting the old
      #| invariant rewrites this to `i * (i + 1) + 2 * (i + 1)`,
      #| which factors as `(i + 1) * (i + 2)`, exactly the invariant for the
      #| next index.
      #|
      #| The loop measure is `n - i`: every step increments `i`, so the measure
      #| strictly decreases until `i == n`. At exit, substituting `i == n`
      #| into the invariant yields the postcondition.
    ),
  }
}
