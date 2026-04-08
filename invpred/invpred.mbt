///|
pub fn binary_search(
  xs : FixedArray[Int],
  key : Int,
) -> Int where {
  proof_require: sorted(xs),
  proof_ensure: result => binary_search_ok(xs, key, result),
} {
  for i = 0, j = xs.length(); i < j; {
    let h = i + (j - i) / 2
    if xs[h] < key {
      continue h + 1, j
    } else {
      continue i, h
    }
  } nobreak {
    if i < xs.length() && xs[i] == key {
      i
    } else {
      -1
    }
  } where {
    proof_invariant: search_window(xs, i, j),
    proof_reasoning: (
      #| This loop narrows a bounded search window for a candidate index.
      #| The machine-checked invariant is intentionally lightweight:
      #| `search_window(xs, i, j)` records only the structural facts
      #| `0 <= i <= j <= xs.length()`.
      #|
      #| That is enough for this package because the postcondition is only a
      #| soundness claim about returned indices. The final `if` after the loop
      #| is what turns the candidate `i` into either a valid witness or `-1`.
      #|
      #| Operationally, sortedness explains the update choice:
      #|   - If `xs[h] < key`, the algorithm continues with the right subwindow.
      #|   - Otherwise it continues with the left subwindow ending at `h`.
      #| Formally, both branches preserve the bounded-window invariant because
      #| `h` is chosen inside the current window.
      #|
      #| The width `j - i` strictly decreases each iteration, so the loop must
      #| stop with `i == j`.
      #|
      #| At exit, we simply check whether `i` is in bounds and stores `key`.
      #| If so, returning `i` is sound; otherwise returning `-1` is also sound
      #| because no invalid index is exposed.
    ),
  }
}
