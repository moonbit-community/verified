///|
/// The proof is the usual order case split: whichever branch wins is an upper bound and
/// one of the inputs.
pub fn max(
  a : Int,
  b : Int,
) -> Int where {
  proof_ensure: result => is_max(a, b, result),
} {
  if a >= b {
    a
  } else {
    b
  }
}
