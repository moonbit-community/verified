///|
#requires(same_length(xs, ys))
#ensures(arrays_eq_ok(xs, ys, result))
pub fn arrays_equal(xs : FixedArray[Int], ys : FixedArray[Int]) -> Int {
  for i = 0, ok = 1; i < xs.length(); {
    let new_ok = if xs[i] == ys[i] { ok } else { 0 }
    continue i + 1, new_ok
  } nobreak {
    ok
  } where {
    invariant: 0 <= i,
    invariant: i <= xs.length(),
    invariant: ok == 0 || ok == 1,
    invariant: eq_upto_when_ok(xs, ys, ok, i),
  }
}
