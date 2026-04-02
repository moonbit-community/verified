///|
pub fn arrays_equal(
  xs : FixedArray[Int],
  ys : FixedArray[Int],
) -> Int where {
  proof_require: same_length(xs, ys),
  proof_ensure: result => arrays_eq_ok(xs, ys, result),
} {
  for i = 0, ok = 1; i < xs.length(); {
    let new_ok = if xs[i] == ys[i] { ok } else { 0 }
    continue i + 1, new_ok
  } nobreak {
    ok
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: ok == 0 || ok == 1,
    proof_invariant: eq_upto_when_ok(xs, ys, ok, i),
    proof_reasoning: (
      #| The flag `ok` summarizes whether all inspected pairs have matched so far.
      #| The quantified invariant says: if `ok == 1`, then the prefix
      #| `xs[0 .. i)` and `ys[0 .. i)` is elementwise equal.
      #|
      #| Initialization holds because the empty prefix is equal vacuously and the
      #| flag starts at `1`.
      #|
      #| On each step we compare `xs[i]` and `ys[i]`:
      #|   - If they are equal, keeping `ok` preserves prefix equality for the
      #|     enlarged prefix.
      #|   - If they differ, setting `ok` to `0` makes the quantified implication
      #|     vacuous, so the invariant remains true.
      #|
      #| The flag is monotone: once a mismatch is seen it never returns to `1`.
      #| The measure `xs.length() - i` also strictly decreases.
      #|
      #| At exit the prefix is the whole array, so `ok == 1` implies full array
      #| equality, which is exactly `arrays_eq_ok`.
    ),
  }
}
