///|
pub fn sort(
  arr : FixedArray[Int],
) -> Int where {
  proof_ensure: result => result == 0 && sorted_desc(arr),
} {
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
      proof_reasoning: (
        #| This pass scans the unsorted suffix from right to left. The frontier
        #| index is `j = n - 1 - t`, and `suffix_head_dominates(arr, j)` means
        #| the element currently at that frontier dominates every element to its
        #| right in the scanned suffix.
        #|
        #| Each compare-and-swap moves the larger of `arr[j - 1]` and `arr[j]`
        #| leftward, so the maximum seen so far keeps bubbling toward index `i`.
        #|
        #| The previously fixed prefix `arr[0 .. i)` is untouched during the
        #| inner loop, so `prefix_dominates_suffix(arr, i)` is preserved.
        #|
        #| The measure `n - 1 - i - t` decreases as `t` increases.
        #|
        #| At exit the frontier has reached `i`, so `arr[i]` dominates the entire
        #| remaining suffix. That is exactly the fact the outer loop needs to
        #| extend the sorted prefix by one element.
      ),
    }
    continue i + 1
  } nobreak {
    0
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: prefix_dominates_suffix(arr, i),
    proof_reasoning: (
      #| After `i` outer iterations, the prefix `arr[0 .. i)` already contains
      #| the `i` largest elements, each dominating every element to its right.
      #|
      #| The inner loop establishes that `arr[i]` becomes the maximum of the
      #| remaining suffix `arr[i .. n)`, so advancing to `i + 1` preserves
      #| `prefix_dominates_suffix`.
      #|
      #| The variant is `n - i`, which decreases each pass.
      #|
      #| When `i == n`, every earlier position dominates every later one, which
      #| is precisely the descending-sorted postcondition.
    ),
  }
}
