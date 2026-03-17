///|
#ensures(find_ok(xs, key, result))
pub fn find(xs : FixedArray[Int], key : Int) -> Int {
  for i = 0, found = -1; i < xs.length(); {
    let new_found = if xs[i] == key && found == -1 { i } else { found }
    continue i + 1, new_found
  } nobreak {
    found
  } where {
    invariant: 0 <= i,
    invariant: i <= xs.length(),
    invariant: found == -1 || (in_bounds(xs, found) && xs[found] == key),
  }
}
