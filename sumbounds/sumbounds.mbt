#requires(in_range(xs, lo, hi))
#ensures(sum_bounded(xs, lo, hi, result))
pub fn bounded_sum(xs : FixedArray[Int], lo : Int, hi : Int) -> Int {
  for i = 0, sum = 0; i < xs.length(); {
    let new_sum = sum + xs[i]
    continue i + 1, new_sum
  } nobreak {
    sum
  } where {
    invariant: 0 <= i,
    invariant: i <= xs.length(),
    invariant: lo * i <= sum,
    invariant: sum <= hi * i,
  }
}
