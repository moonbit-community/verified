///|
pub fn bounded_sum(
  xs : FixedArray[Int],
  lo : Int,
  hi : Int,
) -> Int where {
  proof_require: in_range(xs, lo, hi),
  proof_ensure: result => sum_bounded(xs, lo, hi, result),
} {
  for i = 0, sum = 0; i < xs.length(); {
    let new_sum = sum + xs[i]
    continue i + 1, new_sum
  } nobreak {
    sum
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: lo * i <= sum,
    proof_invariant: sum <= hi * i,
    reasoning: (
      #| After processing the first `i` elements, `sum` is the prefix total and
      #| is sandwiched between the extremal totals `lo * i` and `hi * i`.
      #|
      #| The base case `i = 0`, `sum = 0` satisfies both inequalities exactly.
      #|
      #| For preservation, the precondition gives `lo <= xs[i] <= hi`. Adding the
      #| next element to the old bounds yields
      #| `lo * i + lo <= sum + xs[i] <= hi * i + hi`,
      #| which rewrites to the invariant for `i + 1`.
      #|
      #| The measure `xs.length() - i` decreases because each step increments `i`.
      #|
      #| When the loop finishes, `i == xs.length()`, so the prefix bounds become
      #| the desired bounds for the whole-array sum.
    ),
  }
}
