///|
fn zero_uint() -> UInt where {
  proof_ensure: result => empty_bitmap_inv(result),
} {
  @bitmap32.zero_uint()
}

///|
fn uint_lsr(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_require: valid_idx(idx),
  proof_ensure: result => uint_lsr_post(bitmap, idx, result),
} {
  @bitmap32.uint_lsr(bitmap, idx)
}

///|
fn uint_bit0(
  x : UInt,
) -> Bool where {
  proof_ensure: result => result == @bv32.uint_to_bv(x).nth(0),
} {
  @bitmap32.uint_bit0(x)
}

///|
fn bitmap_add(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx) == false,
  proof_ensure: result => bitmap_add_post(bitmap, idx, result),
} {
  @bitmap32.bitmap_add(bitmap, idx)
}

///|
fn bitmap_remove(
  bitmap : UInt,
  idx : Int,
) -> UInt where {
  proof_require: valid_idx(idx),
  proof_require: mem_value(bitmap, idx),
  proof_ensure: result => bitmap_remove_post(bitmap, idx, result),
} {
  @bitmap32.bitmap_remove(bitmap, idx)
}
