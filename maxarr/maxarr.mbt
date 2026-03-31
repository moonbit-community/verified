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
  }
}
