///|
pub fn count_approvals(
  votes : FixedArray[Int],
) -> Int where {
  proof_require: binary_votes(votes),
  proof_ensure: result => count_approvals_post(votes, result),
} {
  for i = 0, acc = 0; i < votes.length(); {
    let next_acc = if votes[i] == 1 { acc + 1 } else { acc }
    proof_assert next_acc == approval_count_upto(votes, i + 1)
    continue i + 1, next_acc
  } nobreak {
    acc
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= votes.length(),
    proof_invariant: acc == approval_count_upto(votes, i),
    proof_reasoning: (
      #| `acc` tracks the exact number of approvals in the processed prefix
      #| `[0, i)`.
      #|
      #| Because every vote is constrained to `0` or `1`, each iteration either
      #| leaves the count unchanged or increments it by exactly one.
      #|
      #| The explicit `proof_assert` links that concrete update to the logical
      #| `approval_count_upto` summary for the extended prefix.
      #|
      #| The measure `votes.length() - i` decreases because `i` advances by one.
      #|
      #| At exit `i == votes.length()`, so the prefix count becomes the count of
      #| the whole vote slate.
    ),
  }
}

///|
pub fn can_execute(
  votes : FixedArray[Int],
  threshold : Int,
) -> Bool where {
  proof_require: binary_votes(votes),
  proof_require: 0 <= threshold,
  proof_require: threshold <= votes.length(),
  proof_ensure: result => can_execute_post(votes, threshold, result),
} {
  let approvals = count_approvals(votes)
  let result = approvals >= threshold
  proof_assert can_execute_post(votes, threshold, result)
  result
}
