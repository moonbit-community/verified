///|
pub fn find(
  xs : FixedArray[Int],
  key : Int,
) -> Int where {
  proof_ensure: result => find_ok(xs, key, result),
} {
  for i = 0, found = -1; i < xs.length(); {
    let new_found = if xs[i] == key && found == -1 { i } else { found }
    continue i + 1, new_found
  } nobreak {
    found
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: found == -1 || (in_bounds(xs, found) && xs[found] == key),
    proof_reasoning: (
      #| `found` is either the sentinel `-1` meaning “no witness recorded yet”
      #| or a concrete in-bounds index whose array entry equals `key`.
      #| The invariant deliberately proves soundness of the witness, not
      #| minimality or completeness.
      #|
      #| Initially `found = -1`, so the invariant is immediate.
      #|
      #| When scanning `xs[i]`, there are three cases:
      #|   - If `xs[i] == key` and no earlier witness has been stored, we record
      #|     `i`, which is in bounds and satisfies the key-equality clause.
      #|   - If `xs[i] == key` but a witness already exists, we keep the old
      #|     sound witness.
      #|   - If `xs[i] != key`, the witness state is unchanged.
      #|
      #| The measure `xs.length() - i` decreases because `i` advances on every
      #| iteration.
      #|
      #| At exit, the same invariant tells us that any nonnegative result is a
      #| valid matching index, while `-1` remains the designated no-witness value.
    ),
  }
}
