///|
using @bv32 {type BV32}

///|
using @fset {type Fset}

///|
pub fn zero_uint() -> UInt where {
  proof_axiomatized: true,
  proof_ensure: result => empty_bitmap(result),
} {
  0U
}

///|
pub fn uint_lsr(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_ensure: result => uint_lsr_ok(bitmap, idx, result),
} {
  bitmap >> idx
}

///|
pub fn uint_bit0(
  x : UInt,
) -> Bool where {
  proof_axiomatized: true,
  proof_ensure: result => result == @bv32.uint_to_bv(x).nth(0),
} {
  (x & 1U) != 0U
}

///|
pub fn bitmap_add(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx) == false,
  proof_ensure: result => bitmap_add_ok(bitmap, idx, result),
} {
  bitmap | (1U << idx)
}

///|
pub fn bitmap_remove(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_axiomatized: true,
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx),
  proof_ensure: result => bitmap_remove_ok(bitmap, idx, result),
} {
  bitmap & (1U << idx).lnot()
}
