///|
#requires(nonneg(n))
#ensures(gauss_ok(n, result))
pub fn sum_to(n : Int) -> Int {
  for i = 0, sum = 0; i < n; {
    let new_sum = sum + i + 1
    continue i + 1, new_sum
  } nobreak {
    sum
  } where {
    invariant: 0 <= i,
    invariant: i <= n,
    invariant: sum * 2 == i * (i + 1),
  }
}
