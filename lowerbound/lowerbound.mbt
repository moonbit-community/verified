///|
pub fn lower_bound(
  xs : FixedArray[Int],
  key : Int,
) -> Int where {
  proof_require: sorted(xs),
  proof_ensure: result => lower_bound_ok(xs, key, result),
} {
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
    proof_invariant: 0 <= lo,
    proof_invariant: lo <= hi,
    proof_invariant: hi <= xs.length(),
    proof_invariant: all_less_before(xs, key, lo),
    proof_invariant: all_geq_from(xs, key, hi),
    reasoning: (
      #| We maintain a boundary search window `[lo, hi)` with a precise meaning:
      #| every index before `lo` is already proved to store a value `< key`,
      #| and every index from `hi` onward is already proved to store a value
      #| `>= key`.
      #|
      #| Initially `lo = 0` and `hi = xs.length()`, so both facts hold
      #| vacuously.
      #|
      #| When `xs[mid] < key`, sortedness shows every index up to `mid` is also
      #| `< key`, so advancing `lo` to `mid + 1` preserves the left-side fact.
      #| Otherwise `xs[mid] >= key`, and sortedness shows every index from `mid`
      #| onward is `>= key`, so lowering `hi` to `mid` preserves the right-side
      #| fact.
      #|
      #| The variant is `hi - lo`. Since integer division gives `lo <= mid < hi`,
      #| the updates `lo := mid + 1` and `hi := mid` both make that width
      #| strictly smaller.
      #|
      #| At exit `lo == hi`, so the two quantified invariants meet at the same
      #| boundary. That index is exactly the lower bound.
    ),
  }
}
