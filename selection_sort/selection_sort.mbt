///|
pub fn sort(
  arr : FixedArray[Int],
) -> Int where {
  proof_ensure: result => sorted_desc(arr),
} {
  let n = arr.length()
  for i = 0; i < n; {
    let (ub, l) = for j = i + 1, ub = arr[i], l = i; j < n; {
      if arr[j] > ub {
        let next_j = j + 1
        let next_ub = arr[j]
        let next_l = j
        continue next_j, next_ub, next_l
      } else {
        let next_j = j + 1
        continue next_j, ub, l
      }
    } nobreak {
      (ub, l)
    } where {
      proof_invariant: i < j,
      proof_invariant: j <= n,
      proof_invariant: max_in_range(arr, i, j, ub),
      proof_invariant: max_index_in_range(arr, i, j, l),
      proof_invariant: ub == arr[l],
    }
    let old_i = arr[i]
    arr[l] = old_i
    arr[i] = ub
    continue i + 1
  } nobreak {
    0
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: prefix_dominates_suffix(arr, i),
  }
}
