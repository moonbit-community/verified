///|
pub fn cauchy_schwarz_gap(
  xs : FixedArray[Int],
  ys : FixedArray[Int],
) -> Int where {
  proof_require: same_length(xs, ys),
  proof_ensure: result => nonneg(result),
} {
  for i = 0, x2 = 0, y2 = 0, xy = 0, gap = 0; i < xs.length(); {
    let x = xs[i]
    let y = ys[i]
    let new_x2 = x2 + x * x
    let new_y2 = y2 + y * y
    let new_xy = xy + x * y
    let new_gap = new_x2 * new_y2 - new_xy * new_xy
    proof_assert 0 <= new_gap
    continue i + 1, new_x2, new_y2, new_xy, new_gap
  } nobreak {
    gap
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= xs.length(),
    proof_invariant: 0 <= x2,
    proof_invariant: 0 <= y2,
    proof_invariant: gap == x2 * y2 - xy * xy,
    proof_invariant: 0 <= gap,
    proof_invariant: xy * xy <= x2 * y2,
  }
}
