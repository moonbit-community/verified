///|
pub fn first_breach(
  exposures : FixedArray[Int],
  limits : FixedArray[Int],
) -> Option[Int] where {
  proof_require: same_length(exposures, limits),
  proof_ensure: result => first_breach_post(exposures, limits, result),
} {
  let missing = exposures.length()
  let found = for i = 0, first = missing; i < exposures.length(); {
    let new_first = if limits[i] < exposures[i] && first == missing {
      i
    } else {
      first
    }
    continue i + 1, new_first
  } nobreak {
    first
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= exposures.length(),
    proof_invariant:
      first == missing || (
        0 <= first &&
        first < i &&
        limits[first] < exposures[first] &&
        all_safe_before(exposures, limits, first)
      ),
    proof_invariant:
      first != missing || all_safe_before(exposures, limits, i),
    proof_reasoning: (
      #| `i` is the first unchecked account index and `first` is either the
      #| sentinel `missing` or the earliest breach found so far.
      #|
      #| While `first == missing`, every processed account is still known to be
      #| safe. The first time `limits[i] < exposures[i]` holds, we record `i`
      #| and from then on preserve that witness unchanged.
      #|
      #| The witness branch keeps the "earliest breach" fact because the safe
      #| prefix before `first` was already established when the witness was
      #| created. The no-witness branch extends the safe prefix by one.
      #|
      #| The measure `exposures.length() - i` decreases because `i` advances on
      #| every step. At exit, either no witness was ever recorded, which means
      #| the whole array is safe, or `first` is the earliest breached account.
    ),
  }
  if found == missing {
    let result = None
    proof_assert all_safe_before(exposures, limits, exposures.length())
    proof_assert all_safe(exposures, limits)
    proof_assert first_breach_post(exposures, limits, result)
    result
  } else {
    let result = Some(found)
    proof_assert first_breach_post(exposures, limits, result)
    result
  }
}
