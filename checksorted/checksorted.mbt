///|
#ensures(check_sorted_ok(xs, result))
pub fn check_sorted(xs : FixedArray[Int]) -> Int {
  for i = 0, ok = 1; i < xs.length() - 1; {
    let new_ok = if xs[i] <= xs[i + 1] { ok } else { 0 }
    continue i + 1, new_ok
  } nobreak {
    ok
  } where {
    invariant: 0 <= i,
    invariant: ok == 0 || ok == 1,
    invariant: adj_sorted_upto(xs, ok, i + 1),
  }
}
