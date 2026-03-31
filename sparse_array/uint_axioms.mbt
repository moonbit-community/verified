///|
using @bv32 {type BV32}

///|
fn zero_uint() -> UInt where {
  proof_axiomatized: true,
  proof_ensure: result => empty_bitmap(result),
} {
  0U
}

///|
fn uint_lsr(
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
fn uint_bit0(
  x : UInt,
) -> Bool where {
  proof_axiomatized: true,
  proof_ensure: result => result == @bv32.uint_to_bv(x).nth(0),
} {
  (x & 1U) != 0U
}

///|
fn bitmap_add(
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
fn bitmap_remove(
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
