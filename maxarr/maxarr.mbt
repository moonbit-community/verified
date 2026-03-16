#requires(nonempty(xs))
#ensures(is_max_index(xs, result))
pub fn index_of_max(xs : FixedArray[Int]) -> Int {
  for i = 1, best = 0; i < xs.length(); {
    let new_best = if xs[i] > xs[best] { i } else { best }
    continue i + 1, new_best
  } nobreak {
    best
  } where {
    invariant: 1 <= i,
    invariant: i <= xs.length(),
    invariant: 0 <= best,
    invariant: best < i,
    invariant: max_in_prefix(xs, best, i),
  }
}
