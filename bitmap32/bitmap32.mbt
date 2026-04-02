///|
using @bv32 {type BV32}

///|
using @fset {type Fset}

///|
/// These helpers are axiomatized at the proof level: the executable code is tiny, while the
/// comments below record the invariants each bitwise transformation must satisfy.
pub fn zero_uint() -> UInt where {
  proof_axiomatized: true,
  proof_ensure: result => empty_bitmap_inv(result),
} {
  0U
}

///|
/// Shifting is only admissible for a valid index; the postcondition tracks the moved bit.
pub fn uint_lsr(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_ensure: result => uint_lsr_post(bitmap, idx, result),
} {
  bitmap >> idx
}

///|
/// This bridges the low bit of an integer with the bitvector view used by the proof model.
pub fn uint_bit0(
  x : UInt,
) -> Bool where {
  proof_axiomatized: true,
  proof_ensure: result => result == @bv32.uint_to_bv(x).nth(0),
} {
  (x & 1U) != 0U
}

///|
/// Adding a value sets a previously empty bit, so the missing-membership precondition is
/// exactly what makes the bitmap invariant stable.
pub fn bitmap_add(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx) == false,
  proof_ensure: result => bitmap_add_post(bitmap, idx, result),
} {
  bitmap | (1U << idx)
}

///|
/// Removal is the dual case: the bit must already be present so clearing it preserves the
/// abstract set/bitmap correspondence.
pub fn bitmap_remove(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx),
  proof_ensure: result => bitmap_remove_post(bitmap, idx, result),
} {
  bitmap & (1U << idx).lnot()
}
