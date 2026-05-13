///|
pub fn[T : Compare] check_sorted(
  xs : FixedArray[T],
) -> Int where {
  proof_ensure: result => check_sorted_ok(xs, result),
} {
  for i = 0, ok = 1; i < xs.length() - 1; {
    let new_ok = if xs[i] <= xs[i + 1] { ok } else { 0 }
    continue i + 1, new_ok
  } nobreak {
    ok
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: ok == 0 || ok == 1,
    proof_invariant: adj_sorted_upto(xs, ok, i + 1),
    proof_reasoning: (
      #| The flag `ok` records whether every adjacent pair examined so far is in
      #| nondecreasing order. The predicate `adj_sorted_upto(xs, ok, i + 1)`
      #| packages that statement over the prefix ending at `i`.
      #|
      #| Initially no adjacent pair has been checked, so the property is vacuous.
      #|
      #| Each iteration inspects the new boundary pair `(i, i + 1)`:
      #|   - If `xs[i] <= xs[i + 1]`, keeping `ok` extends the ordered prefix.
      #|   - Otherwise we set `ok = 0`, and the quantified implication becomes
      #|     vacuous from that point on.
      #|
      #| The measure `xs.length() - 1 - i` decreases because `i` advances by one.
      #|
      #| When the loop exits, the prefix covers all adjacent pairs in the array,
      #| so `ok == 1` implies the whole array is sorted.
    ),
  }
}
