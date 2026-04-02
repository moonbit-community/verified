///|
pub fn sort(
  arr : FixedArray[Int],
) -> Int where {
  proof_ensure: result => result == 0 && sorted_desc(arr),
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
      proof_reasoning: (
        #| The inner scan maintains a concrete witness `l` and value `ub` such
        #| that `ub == arr[l]` and `ub` is maximal on the visited range
        #| `arr[i .. j)`.
        #|
        #| Initialization uses the one-element range `[i, i + 1)`, where
        #| `ub = arr[i]` and `l = i` are trivially correct.
        #|
        #| On each step we inspect `arr[j]`:
        #|   - If `arr[j] > ub`, we update both the witness and the value.
        #|   - Otherwise the old witness remains maximal for the extended range.
        #|
        #| The measure `n - j` decreases as the scan advances.
        #|
        #| At exit `j == n`, so `ub` and `l` describe a maximum element of the
        #| entire unsorted suffix `arr[i .. n)`.
      ),
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
    proof_reasoning: (
      #| After each iteration, the prefix `arr[0 .. i)` contains the `i`
      #| greatest elements of the array in descending order relative to the
      #| remaining suffix.
      #|
      #| The inner scan finds a maximum of `arr[i .. n)`, and the swap places
      #| that maximum at index `i`. Therefore extending the prefix to `i + 1`
      #| preserves `prefix_dominates_suffix`.
      #|
      #| The measure `n - i` decreases by one each outer step.
      #|
      #| At exit the prefix is the whole array, so every earlier element
      #| dominates every later one, which means the array is sorted descending.
    ),
  }
}
