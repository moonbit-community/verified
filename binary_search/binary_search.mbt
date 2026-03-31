///|
pub fn binary_search(
  xs : FixedArray[Int],
  key : Int,
) -> Int? where {
  proof_require: sorted(xs),
  proof_ensure: result => binary_search_ok(xs, key, result),
} {
  for i = 0, j = xs.length(); i < j; {
    let h = i + (j - i) / 2
    if xs[h] < key {
      continue h + 1, j
    } else if xs[h] > key {
      continue i, h
    } else {
      break Some(h)
    }
  } nobreak {
    None
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= j,
    proof_invariant: j <= xs.length(),
    proof_invariant: all_less_before(xs, key, i),
    proof_invariant: all_greater_from(xs, key, j),
    proof_yield: res => binary_search_ok(xs, key, res),
  }
}
