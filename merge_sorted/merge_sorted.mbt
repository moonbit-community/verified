using @fset {type Fset}

///|
pub fn merge(
  xs : FixedArray[Int],
  ys : FixedArray[Int],
) -> FixedArray[Int] where {
  proof_require: sorted(xs),
  proof_require: sorted(ys),
  proof_ensure: result => merge_ok(xs, ys, result),
} {
  let total = xs.length() + ys.length()
  let out = FixedArray::make(total, 0)
  let result = for k = 0, i = 0, j = 0; k < total; {
    if i == xs.length() {
      out[k] = ys[j]
      proof_assert j < ys.length()
      proof_assert out[k] == ys[j]
      proof_assert valid_prefix(ys, j + 1)
      proof_assert valid_prefix(out, k + 1)
      proof_assert prefix_counts_merge(xs, i, ys, j, out, k)
      proof_assert count_prefix_step_holds(out, k, ys[j])
      proof_assert count_prefix_step_holds(ys, j, ys[j])
      proof_assert prefix_counts_merge(xs, i, ys, j + 1, out, k + 1)
      continue k + 1, i, j + 1
    } else if j == ys.length() {
      out[k] = xs[i]
      proof_assert i < xs.length()
      proof_assert out[k] == xs[i]
      proof_assert valid_prefix(xs, i + 1)
      proof_assert valid_prefix(out, k + 1)
      proof_assert prefix_counts_merge(xs, i, ys, j, out, k)
      proof_assert count_prefix_step_holds(out, k, xs[i])
      proof_assert count_prefix_step_holds(xs, i, xs[i])
      proof_assert prefix_counts_merge(xs, i + 1, ys, j, out, k + 1)
      continue k + 1, i + 1, j
    } else if xs[i] <= ys[j] {
      out[k] = xs[i]
      proof_assert out[k] == xs[i]
      proof_assert valid_prefix(xs, i + 1)
      proof_assert valid_prefix(out, k + 1)
      proof_assert prefix_counts_merge(xs, i, ys, j, out, k)
      proof_assert count_prefix_step_holds(out, k, xs[i])
      proof_assert count_prefix_step_holds(xs, i, xs[i])
      proof_assert prefix_counts_merge(xs, i + 1, ys, j, out, k + 1)
      continue k + 1, i + 1, j
    } else {
      out[k] = ys[j]
      proof_assert out[k] == ys[j]
      proof_assert valid_prefix(ys, j + 1)
      proof_assert valid_prefix(out, k + 1)
      proof_assert prefix_counts_merge(xs, i, ys, j, out, k)
      proof_assert count_prefix_step_holds(out, k, ys[j])
      proof_assert count_prefix_step_holds(ys, j, ys[j])
      proof_assert prefix_counts_merge(xs, i, ys, j + 1, out, k + 1)
      continue k + 1, i, j + 1
    }
  } nobreak {
    out
  } where {
    proof_invariant: valid_prefix(xs, i),
    proof_invariant: valid_prefix(ys, j),
    proof_invariant: valid_prefix(out, k),
    proof_invariant: k == i + j,
    proof_invariant: sorted_prefix(out, k),
    proof_invariant: prefix_counts_merge(xs, i, ys, j, out, k),
    proof_invariant: i >= xs.length() || prefix_le_value(out, k, xs[i]),
    proof_invariant: j >= ys.length() || prefix_le_value(out, k, ys[j]),
    reasoning: (
      #| This loop is the core merge step used by mergesort. The processed
      #| prefixes `xs[0 .. i)` and `ys[0 .. j)` have already been copied into
      #| `out[0 .. k)`, with `k == i + j`.
      #|
      #| Two facts are preserved together:
      #|   - `sorted_prefix(out, k)` says the produced prefix is ordered.
      #|   - `prefix_counts_merge(xs, i, ys, j, out, k)` says it contains
      #|     exactly the multiset union of the consumed input prefixes.
      #|
      #| The head comparison chooses the smaller remaining element, so appending
      #| it keeps the output prefix sorted. Because we copy exactly one head
      #| element each time, the count model advances by the same one-element
      #| delta on both the output prefix and the corresponding consumed input
      #| prefix.
      #|
      #| The side conditions `prefix_le_value(out, k, xs[i])` and its `ys`
      #| analogue say every produced element is bounded by each current head,
      #| which is the bridge needed to preserve sortedness when a new head is
      #| appended.
      #|
      #| The loop is driven directly by `k < total`, so the variant is
      #| `total - k`. Each branch copies exactly one element and increments `k`.
    ),
  }
  result
}
