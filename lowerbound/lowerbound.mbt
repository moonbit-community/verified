///|
#requires(sorted(xs))
#ensures(lower_bound_ok(xs, key, result))
pub fn lower_bound(xs : FixedArray[Int], key : Int) -> Int {
  for lo = 0, hi = xs.length(); lo < hi; {
    let mid = lo + (hi - lo) / 2
    if xs[mid] < key {
      continue mid + 1, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  } where {
    invariant: 0 <= lo,
    invariant: lo <= hi,
    invariant: hi <= xs.length(),
    invariant: all_less_before(xs, key, lo),
    invariant: all_geq_from(xs, key, hi),
  }
}
