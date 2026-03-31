///|
#ensures(sorted_desc(arr))
pub fn sort(arr : FixedArray[Int]) -> Int {
  let n = arr.length()
  for i = 0; i < n; {
    let _ = for t = 0; t < n - 1 - i; {
      let j = n - 1 - t
      if arr[j - 1] < arr[j] {
        let tmp = arr[j]
        arr[j] = arr[j - 1]
        arr[j - 1] = tmp
      }
      continue t + 1
    } nobreak {
      i
    } where {
      proof_invariant: 0 <= t,
      proof_invariant: t <= n - 1 - i,
      proof_invariant: i <= n - 1 - t,
      proof_invariant: suffix_head_dominates(arr, n - 1 - t),
      proof_invariant: prefix_dominates_suffix(arr, i),
    }
    continue i + 1
  } nobreak {
    0
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: prefix_dominates_suffix(arr, i),
  }
}
