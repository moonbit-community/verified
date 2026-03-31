///|
using @fmap {type Fmap}

///|
using @fset {type Fset}

///|
pub struct SparseArray {
  bitmap : UInt
  data : FixedArray[Int]
} derive(Eq)

///|
fn bitmap_mem(
  bitmap : UInt,
  idx : Int,
) -> Bool where {
  proof_require: valid_idx(idx),
  proof_ensure: result => result == mem_value(bitmap, idx),
} {
  let shifted = uint_lsr(bitmap, idx)
  let result = uint_bit0(shifted)
  proof_assert result == mem_value(bitmap, idx)
  result
}

///|
fn bitmap_rank(
  bitmap : UInt,
  idx : Int,
) -> Int where {
  proof_require: valid_prefix_idx(idx),
  proof_ensure: result => result == rank_value(bitmap, idx, 0),
} {
  for j = 0, acc = 0; j < idx; {
    let next_acc = if bitmap_mem(bitmap, j) { acc + 1 } else { acc }
    proof_assert next_acc == rank_value(bitmap, j + 1, 0)
    continue j + 1, next_acc
  } nobreak {
    acc
  } where {
    proof_invariant: 0 <= j,
    proof_invariant: j <= idx,
    proof_invariant: acc == rank_value(bitmap, j, 0),
  }
}

///|
pub fn empty() -> SparseArray where {
  proof_ensure: result => empty_bitmap_inv(result.bitmap),
  proof_ensure: result => result.data.length() == 0,
  proof_ensure: result => empty_post(result),
} {
  let result = { bitmap: zero_uint(), data: FixedArray::make(0, 0) }
  proof_assert sparse_array_inv(result)
  proof_assert domain(result.bitmap).eq(@fset.fset_empty())
  proof_assert model(result).eq(@fmap.fmap_empty())
  proof_assert empty_post(result)
  result
}

///|
pub fn singleton(
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: valid_idx(idx),
  proof_ensure: result => singleton_post(result, idx, value),
} {
  let empty = zero_uint()
  proof_assert empty_bitmap_inv(empty)
  let bitmap = bitmap_add(empty, idx)
  proof_assert bitmap_add_post(empty, idx, bitmap)
  proof_assert singleton_bitmap_inv(bitmap, idx)
  let data = FixedArray::make(1, value)
  proof_assert data.length() == 1
  proof_assert data[0] == value
  let result = { bitmap, data }
  proof_assert count_value(result.bitmap, 0) == 1
  proof_assert rank_value(result.bitmap, idx, 0) == 0
  proof_assert sparse_array_inv(result)
  proof_assert domain(result.bitmap).eq(@fset.fset_empty().add(idx))
  proof_assert model(result).mem(idx)
  proof_assert model(result).find(idx) == value
  proof_assert singleton_post(result, idx, value)
  result
}

///|
pub fn SparseArray::get(
  self : SparseArray,
  idx : Int,
) -> Int? where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_ensure: result => get_post(self, idx, result),
} {
  if bitmap_mem(self.bitmap, idx) {
    Some(self.data[bitmap_rank(self.bitmap, idx)])
  } else {
    None
  }
}

///|
pub fn SparseArray::add(
  self : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_require: model(self).mem(idx) == false,
  proof_ensure: result => sparse_array_inv(result),
  proof_ensure: result => model(result).eq(model(self).add(idx, value)),
} {
  let old_data = self.data
  let old_len = old_data.length()
  let pos = bitmap_rank(self.bitmap, idx)
  proof_assert 0 <= pos
  proof_assert pos <= old_len
  let new_data = FixedArray::make(old_len + 1, value)
  proof_assert pos < new_data.length()
  for i = 0; i < pos; {
    new_data[i] = old_data[i]
    continue i + 1
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= pos,
    proof_invariant: add_prefix_ok(old_data, new_data, pos, i),
  }
  new_data[pos] = value
  proof_assert add_fill_ok(old_data, new_data, pos, value, pos)
  for i = pos; i < old_len; {
    new_data[i + 1] = old_data[i]
    continue i + 1
  } where {
    proof_invariant: pos <= i,
    proof_invariant: i <= old_len,
    proof_invariant: add_fill_ok(old_data, new_data, pos, value, i),
  }
  let result = { bitmap: bitmap_add(self.bitmap, idx), data: new_data }
  proof_assert add_data_ok(self, idx, value, result)
  proof_assert add_post(self, idx, value, result)
  result
}

///|
pub fn SparseArray::replace(
  self : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_require: model(self).mem(idx),
  proof_ensure: result => sparse_array_inv(result),
  proof_ensure: result => model(result).eq(model(self).add(idx, value)),
} {
  let old_data = self.data
  let old_len = old_data.length()
  let pos = bitmap_rank(self.bitmap, idx)
  proof_assert 0 <= pos
  proof_assert pos < old_len
  let new_data = FixedArray::make(old_len, value)
  proof_assert new_data.length() == old_len
  proof_assert new_data[pos] == value
  for i = 0; i < old_len; {
    if i != pos {
      new_data[i] = old_data[i]
    }
    continue i + 1
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= old_len,
    proof_invariant: replace_prefix_ok(old_data, new_data, pos, value, i),
  }
  let result = { bitmap: self.bitmap, data: new_data }
  proof_assert replace_data_ok(self, idx, value, result)
  proof_assert replace_post(self, idx, value, result)
  result
}

///|
pub fn SparseArray::remove(
  self : SparseArray,
  idx : Int,
) -> SparseArray where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_require: model(self).mem(idx),
  proof_ensure: result => sparse_array_inv(result),
  proof_ensure: result => model(result).eq(model(self).remove(idx)),
} {
  let old_data = self.data
  let old_len = old_data.length()
  if old_len == 1 {
    let result = empty()
    proof_assert remove_empty_post(self, idx, result)
    result
  } else {
    let pos = bitmap_rank(self.bitmap, idx)
    let new_data = FixedArray::make(old_len - 1, old_data[0])
    for i = 0; i < pos; {
      new_data[i] = old_data[i]
      continue i + 1
    } where {
      proof_invariant: 0 <= i,
      proof_invariant: i <= pos,
      proof_invariant: remove_prefix_ok(old_data, new_data, pos, i),
    }
    proof_assert remove_fill_ok(old_data, new_data, pos, pos)
    for i = pos; i < old_len - 1; {
      new_data[i] = old_data[i + 1]
      continue i + 1
    } where {
      proof_invariant: pos <= i,
      proof_invariant: i <= old_len - 1,
      proof_invariant: remove_fill_ok(old_data, new_data, pos, i),
    }
    let result = { bitmap: bitmap_remove(self.bitmap, idx), data: new_data }
    proof_assert remove_data_ok(self, idx, result)
    proof_assert remove_post(self, idx, result)
    result
  }
}

///|
pub fn SparseArray::length(
  self : SparseArray,
) -> Int where {
  proof_require: sparse_array_inv(self),
  proof_ensure: result => result == model(self).size(),
} {
  proof_assert length_post(self)
  self.data.length()
}
