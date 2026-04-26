///|
/// Proof-side mathematical integers, backed by Why3's unbounded `int`.
///
/// This type is intended for logical specifications and imported proof symbols,
/// not executable runtime arithmetic.
#proof_external("int.Int", "int")
pub type MathInt
