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
  }
}
