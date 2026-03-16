#ensures(count_bounded(xs, result))
pub fn count_nonneg(xs : FixedArray[Int]) -> Int {
  for i = 0, count = 0; i < xs.length(); {
    if xs[i] >= 0 {
      continue i + 1, count + 1
    } else {
      continue i + 1, count
    }
  } nobreak {
    count
  } where {
    invariant: 0 <= i,
    invariant: i <= xs.length(),
    invariant: 0 <= count,
    invariant: count <= i,
  }
}
