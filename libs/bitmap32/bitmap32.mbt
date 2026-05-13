///|
using @fset {type Fset}

///|
pub fn zero_uint() -> UInt where {
  proof_ensure: result => empty_bitmap_inv(result),
} {
  0U
}

///|
/// Trusted because `moon prove` does not currently lower UInt shifts in
/// untrusted contracted bodies. The postcondition tracks the shifted bitvector.
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
/// Trusted because `moon prove` does not currently lower UInt bitwise `&` in
/// untrusted contracted bodies. This bridges the low bit with the proof model.
pub fn uint_bit0(
  x : UInt,
) -> Bool where {
  proof_axiomatized: true,
  proof_ensure: result => result == @bv32.uint_to_bv(x).nth(0),
} {
  (x & 1U) != 0U
}

///|
/// Trusted because `moon prove` does not currently lower UInt bitwise `|` and
/// shifts in untrusted contracted bodies.
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
/// Trusted because `moon prove` does not currently lower UInt bitwise `&`,
/// `lnot`, and shifts in untrusted contracted bodies.
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
