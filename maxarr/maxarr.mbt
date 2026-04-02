///|
pub fn index_of_max(
  xs : FixedArray[Int],
) -> Int where {
  proof_require: nonempty(xs),
  proof_ensure: result => is_max_index(xs, result),
} {
  for i = 1, best = 0; i < xs.length(); {
    let new_best = if xs[i] > xs[best] { i } else { best }
    continue i + 1, new_best
  } nobreak {
    best
  } where {
    proof_invariant: 1 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: 0 <= best,
    proof_invariant: best < i,
    proof_invariant: max_in_prefix(xs, best, i),
    proof_reasoning: (
      #| `best` is always an index of a maximal element in the processed prefix
      #| `xs[0 .. i)`. The bounds invariants keep that witness index valid.
      #|
      #| Initially the processed prefix has one element, so `best = 0` is
      #| trivially maximal.
      #|
      #| When we inspect `xs[i]`, there are only two possibilities:
      #|   - If `xs[i] > xs[best]`, the new element becomes the unique best
      #|     witness for the enlarged prefix.
      #|   - Otherwise the previous witness still dominates the enlarged prefix.
      #|
      #| The measure `xs.length() - i` decreases because `i` is incremented on
      #| every step.
      #|
      #| At exit `i == xs.length()`, so `max_in_prefix(xs, best, i)` is exactly
      #| the statement that `best` indexes a global maximum.
    ),
  }
}
