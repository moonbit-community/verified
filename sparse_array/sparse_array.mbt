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
  proof_ensure: result => empty_bitmap(result.bitmap),
  proof_ensure: result => result.data.length() == 0,
  proof_ensure: result => empty_abs_ok(result),
} {
  let result = { bitmap: zero_uint(), data: FixedArray::make(0, 0) }
  proof_assert sparse_ok(result)
  proof_assert domain(result.bitmap).eq(@fset.fset_empty())
  proof_assert abs(result).eq(@fmap.fmap_empty())
  proof_assert empty_abs_ok(result)
  result
}

///|
pub fn singleton(
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: valid_idx(idx),
  proof_ensure: result => singleton_abs_ok(result, idx, value),
} {
  let empty = zero_uint()
  proof_assert empty_bitmap(empty)
  let bitmap = bitmap_add(empty, idx)
  proof_assert bitmap_add_ok(empty, idx, bitmap)
  proof_assert singleton_bitmap_ok(bitmap, idx)
  let data = FixedArray::make(1, value)
  proof_assert data.length() == 1
  proof_assert data[0] == value
  let result = { bitmap, data }
  proof_assert count_value(result.bitmap, 0) == 1
  proof_assert rank_value(result.bitmap, idx, 0) == 0
  proof_assert sparse_ok(result)
  proof_assert domain(result.bitmap).eq(@fset.fset_empty().add(idx))
  proof_assert abs(result).mem(idx)
  proof_assert abs(result).find(idx) == value
  proof_assert singleton_abs_ok(result, idx, value)
  result
}

///|
pub fn get(
  sa : SparseArray,
  idx : Int,
) -> Int? where {
  proof_require: sparse_ok(sa),
  proof_require: valid_idx(idx),
  proof_ensure: result => get_ok(sa, idx, result),
} {
  if bitmap_mem(sa.bitmap, idx) {
    Some(sa.data[bitmap_rank(sa.bitmap, idx)])
  } else {
    None
  }
}

///|
pub fn add(
  sa : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: sparse_ok(sa),
  proof_require: valid_idx(idx),
  proof_require: abs(sa).mem(idx) == false,
  proof_ensure: result => sparse_ok(result),
  proof_ensure: result => abs(result).eq(abs(sa).add(idx, value)),
} {
  let old_data = sa.data
  let old_len = old_data.length()
  let pos = bitmap_rank(sa.bitmap, idx)
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
  let result = { bitmap: bitmap_add(sa.bitmap, idx), data: new_data }
  proof_assert add_data_ok(sa, idx, value, result)
  proof_assert add_abs_ok(sa, idx, value, result)
  result
}

///|
pub fn replace(
  sa : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray where {
  proof_require: sparse_ok(sa),
  proof_require: valid_idx(idx),
  proof_require: abs(sa).mem(idx),
  proof_ensure: result => sparse_ok(result),
  proof_ensure: result => abs(result).eq(abs(sa).add(idx, value)),
} {
  let old_data = sa.data
  let old_len = old_data.length()
  let pos = bitmap_rank(sa.bitmap, idx)
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
  let result = { bitmap: sa.bitmap, data: new_data }
  proof_assert replace_data_ok(sa, idx, value, result)
  proof_assert replace_abs_ok(sa, idx, value, result)
  result
}

///|
pub fn remove(
  sa : SparseArray,
  idx : Int,
) -> SparseArray where {
  proof_require: sparse_ok(sa),
  proof_require: valid_idx(idx),
  proof_require: abs(sa).mem(idx),
  proof_ensure: result => sparse_ok(result),
  proof_ensure: result => abs(result).eq(abs(sa).remove(idx)),
} {
  let old_data = sa.data
  let old_len = old_data.length()
  if old_len == 1 {
    let result = empty()
    proof_assert remove_empty_abs_ok(sa, idx, result)
    result
  } else {
    let pos = bitmap_rank(sa.bitmap, idx)
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
    let result = { bitmap: bitmap_remove(sa.bitmap, idx), data: new_data }
    proof_assert remove_data_ok(sa, idx, result)
    proof_assert remove_abs_ok(sa, idx, result)
    result
  }
}

///|
pub fn length(
  sa : SparseArray,
) -> Int where {
  proof_require: sparse_ok(sa),
  proof_ensure: result => result == abs(sa).size(),
} {
  proof_assert length_abs_ok(sa)
  sa.data.length()
}

///|
pub fn SparseArray::get(self : SparseArray, idx : Int) -> Int? {
  get(self, idx)
}

///|
pub fn SparseArray::add(
  self : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray {
  add(self, idx, value)
}

///|
pub fn SparseArray::replace(
  self : SparseArray,
  idx : Int,
  value : Int,
) -> SparseArray {
  replace(self, idx, value)
}

///|
pub fn SparseArray::remove(self : SparseArray, idx : Int) -> SparseArray {
  remove(self, idx)
}

///|
#alias(size, deprecated)
pub fn SparseArray::length(self : SparseArray) -> Int {
  length(self)
}
