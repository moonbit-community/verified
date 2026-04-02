///|
pub fn binary_search(
  xs : FixedArray[Int],
  key : Int,
) -> Int? where {
  proof_require: sorted(xs),
  proof_ensure: result => binary_search_ok(xs, key, result),
} {
  for i = 0, j = xs.length(); i < j; {
    let h = i + (j - i) / 2
    if xs[h] < key {
      continue h + 1, j
    } else if xs[h] > key {
      continue i, h
    } else {
      break Some(h)
    }
  } nobreak {
    None
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= j,
    proof_invariant: j <= xs.length(),
    proof_invariant: all_less_before(xs, key, i),
    proof_invariant: all_greater_from(xs, key, j),
    proof_yield: res => binary_search_ok(xs, key, res),
    proof_reasoning: (
      #| The loop maintains a candidate window `[i, j)`:
      #| every index before `i` is known to hold a value `< key`, and every
      #| index from `j` onward is known to hold a value `> key`.
      #|
      #| Initialization is vacuous with `i = 0` and `j = xs.length()`, so the
      #| excluded regions are empty.
      #|
      #| At midpoint `h` there are three cases:
      #|   - `xs[h] < key`: by sortedness, every index up to `h` is `< key`, so
      #|     moving the left boundary to `h + 1` preserves the exclusion facts.
      #|   - `xs[h] > key`: by sortedness, every index from `h` onward is `> key`,
      #|     so moving the right boundary to `h` is safe.
      #|   - `xs[h] == key`: the yielded witness `Some(h)` is immediately correct.
      #|
      #| The variant is the window width `j - i`. Because `h` lies inside the
      #| current window, either update removes at least one position, so the
      #| width strictly decreases.
      #|
      #| If the loop exits normally, `i == j`. The two exclusion invariants then
      #| cover the whole array, so no index can contain `key`, which justifies
      #| returning `None`.
    ),
  }
}
