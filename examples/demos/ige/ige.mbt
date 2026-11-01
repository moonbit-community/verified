///|
#proof_external("bv.BV128", "t")
priv type BV128

///|
/// Proof-side message model: a list of 16-byte blocks. `Int` is unbounded in
/// proofs, so blocks range over `[0, 2^128)`; there is no executable IGE here.
pub(all) enum Blocks {
  Nil
  Cons(Int32, Blocks)
}

///|
/// IGE chaining state: the previous ciphertext and plaintext blocks.
pub(all) struct Iv {
  c : Int32
  p : Int32
}
