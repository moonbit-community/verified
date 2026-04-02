///|
pub fn count_nonneg(
  xs : FixedArray[Int],
) -> Int where {
  proof_ensure: result => count_bounded(xs, result),
} {
  for i = 0, count = 0; i < xs.length(); {
    if xs[i] >= 0 {
      continue i + 1, count + 1
    } else {
      continue i + 1, count
    }
  } nobreak {
    count
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: 0 <= count,
    proof_invariant: count <= i,
    reasoning: (
      #| This proof only tracks bounds on the accumulator, not an exact counting
      #| predicate. At each loop boundary, `count` is known to be nonnegative
      #| and no larger than the processed prefix length `i`.
      #|
      #| Initialization holds at `i = 0`, `count = 0`.
      #|
      #| Each step inspects `xs[i]`:
      #|   - If `xs[i] >= 0`, incrementing `count` preserves `0 <= count` and
      #|     still keeps `count <= i + 1`.
      #|   - Otherwise leaving `count` unchanged preserves the same bounds for
      #|     the larger prefix.
      #|
      #| In both branches `i` increases by one, so the measure `xs.length() - i`
      #| strictly decreases.
      #|
      #| At exit `i == xs.length()`, those same numeric bounds become exactly
      #| the postcondition `count_bounded(xs, count)`.
    ),
  }
}
