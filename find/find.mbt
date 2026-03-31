///|
pub fn find(
  xs : FixedArray[Int],
  key : Int,
) -> Int where {
  proof_ensure: result => find_ok(xs, key, result),
} {
  for i = 0, found = -1; i < xs.length(); {
    let new_found = if xs[i] == key && found == -1 { i } else { found }
    continue i + 1, new_found
  } nobreak {
    found
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: found == -1 || (in_bounds(xs, found) && xs[found] == key),
  }
}
