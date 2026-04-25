///|
using @fmap {type Fmap}

///|
using @fset {type Fset}

///|
pub struct SparseArray[T] {
  bitmap : UInt
  data : FixedArray[T]
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
    proof_reasoning: (
      #| `acc` is the concrete running count of set bits in the prefix
      #| `[0, j)`, while `rank_value(bitmap, j, 0)` is the abstract set-based
      #| definition of the same quantity.
      #|
      #| The invariant equates those two views. Each iteration inspects bit `j`
      #| and either leaves the count unchanged or increments it by one. The
      #| explicit `proof_assert` bridges that step to the abstract rank at `j + 1`.
      #|
      #| The measure `idx - j` decreases because `j` advances by one.
      #|
      #| At exit `j == idx`, so the concrete counter `acc` equals the desired
      #| prefix rank.
    ),
  }
}

///|
pub fn[T] empty() -> SparseArray[T] {
  { bitmap: zero_uint(), data: [] }
}

///|
pub fn[T : Eq] singleton(
  idx : Int,
  value : T,
) -> SparseArray[T] where {
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
  proof_assert data[0].equal(value)
  let result = { bitmap, data }
  proof_assert count_value(result.bitmap, 0) == 1
  proof_assert rank_value(result.bitmap, idx, 0) == 0
  proof_assert sparse_array_inv(result)
  proof_assert domain(result.bitmap).eq(@fset.fset_empty().add(idx))
  proof_assert model(result).mem(idx)
  proof_assert model(result).find(idx).equal(value)
  proof_assert singleton_post(result, idx, value)
  result
}

///|
pub fn[T : Eq] SparseArray::get(
  self : SparseArray[T],
  idx : Int,
) -> T? where {
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
pub fn[T : Eq] SparseArray::add(
  self : SparseArray[T],
  idx : Int,
  value : T,
) -> SparseArray[T] where {
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
    proof_reasoning: (
      #| This loop copies the unchanged prefix `[0, pos)` into the larger array.
      #| `add_prefix_ok` records exactly which prefix entries already agree with
      #| the old data while reserving one extra slot for insertion.
      #|
      #| Each step copies one more element verbatim, so the copied prefix grows
      #| from length `i` to length `i + 1`.
      #|
      #| The measure `pos - i` decreases monotonically.
      #|
      #| At exit, every index before `pos` has been copied and the insertion slot
      #| is ready to be filled.
    ),
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
    proof_reasoning: (
      #| After writing `new_data[pos] = value`, the remaining task is to shift
      #| the old suffix `[pos, old_len)` one position to the right.
      #|
      #| `add_fill_ok` states that the prefix before `pos` is already copied, the
      #| inserted value is fixed at `pos`, and the old suffix has been shifted
      #| correctly for the processed range `[pos, i)`.
      #|
      #| Each iteration extends that shifted range by copying `old_data[i]` into
      #| `new_data[i + 1]`.
      #|
      #| The measure `old_len - i` decreases, and at exit the whole suffix has
      #| been shifted, yielding the data-layout part of `add_post`.
    ),
  }
  let result = { bitmap: bitmap_add(self.bitmap, idx), data: new_data }
  proof_assert bitmap_add_post(self.bitmap, idx, result.bitmap)
  proof_assert add_data_ok(self, idx, value, result)
  proof_assert mem_value(self.bitmap, idx) == false
  proof_assert result.data.length() == self.data.length() + 1
  proof_assert self.data.length() == count_value(self.bitmap, 0)
  proof_assert count_value(result.bitmap, 0) == count_value(self.bitmap, 0) + 1
  proof_assert result.data.length() == count_value(result.bitmap, 0)
  proof_assert rank_value(result.bitmap, idx, 0) ==
    rank_value(self.bitmap, idx, 0)
  proof_assert ∀ i : Int,
    valid_idx(i) && mem_value(result.bitmap, i) && i <= idx →
    rank_value(result.bitmap, i, 0) == rank_value(self.bitmap, i, 0)
  proof_assert ∀ i : Int,
    valid_idx(i) && mem_value(result.bitmap, i) && idx < i →
    rank_value(result.bitmap, i, 0) == rank_value(self.bitmap, i, 0) + 1
  proof_assert ∀ i : Int,
    valid_idx(i) && mem_value(result.bitmap, i) && i == idx →
    0 <= rank_value(result.bitmap, i, 0) &&
    rank_value(result.bitmap, i, 0) < result.data.length()
  proof_assert ∀ i : Int,
    valid_idx(i) && mem_value(result.bitmap, i) && i != idx →
    0 <= rank_value(result.bitmap, i, 0) &&
    rank_value(result.bitmap, i, 0) < result.data.length()
  proof_assert sparse_array_inv(result)
  proof_assert ∀ j : Int,
    model(result).mem(j) == model(self).add(idx, value).mem(j)
  proof_assert model(result).find(idx).equal(value)
  proof_assert ∀ j : Int, model(result).mem(j) → valid_idx(j)
  proof_assert ∀ j : Int,
    model(result).mem(j) && j == idx →
    model(result).find(j).equal(model(self).add(idx, value).find(j))
  proof_assert ∀ j : Int,
    model(result).mem(j) && j != idx →
    model(result).find(j).equal(model(self).find(j))
  proof_assert ∀ j : Int,
    model(result).mem(j) && j != idx →
    model(result).find(j).equal(model(self).add(idx, value).find(j))
  proof_assert ∀ j : Int,
    model(result).mem(j) →
    model(result).find(j).equal(model(self).add(idx, value).find(j))
  proof_assert fmap_eq_hyp_local(model(result), model(self).add(idx, value))
  proof_assert model(result).eq(model(self).add(idx, value))
  proof_assert add_post(self, idx, value, result)
  result
}

///|
pub fn[T : Eq] SparseArray::replace(
  self : SparseArray[T],
  idx : Int,
  value : T,
) -> SparseArray[T] where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_require: model(self).mem(idx),
  proof_ensure: result => replace_post(self, idx, value, result),
} {
  let old_data = self.data
  let old_len = old_data.length()
  let pos = bitmap_rank(self.bitmap, idx)
  proof_assert 0 <= pos
  proof_assert pos < old_len
  let new_data = FixedArray::make(old_len, value)
  proof_assert new_data.length() == old_len
  proof_assert new_data[pos].equal(value)
  for i = 0; i < old_len; {
    if i != pos {
      new_data[i] = old_data[i]
    }
    continue i + 1
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= old_len,
    proof_invariant: replace_prefix_ok(old_data, new_data, pos, value, i),
    proof_reasoning: (
      #| Replacement keeps the bitmap and array length unchanged; only the slot
      #| at `pos` should differ. We initialize `new_data[pos]` with `value`
      #| before the loop and then copy every other position from the old array.
      #|
      #| `replace_prefix_ok` captures that all processed indices except `pos`
      #| already agree with `old_data`, while the distinguished slot keeps the
      #| new value.
      #|
      #| Each iteration extends the copied prefix by one index, either writing a
      #| copy or skipping `pos`.
      #|
      #| The measure `old_len - i` decreases, and at exit every position has the
      #| intended value, giving `replace_data_ok`.
    ),
  }
  let result = { bitmap: self.bitmap, data: new_data }
  proof_assert replace_data_ok(self, idx, value, result)
  proof_assert replace_post(self, idx, value, result)
  result
}

///|
pub fn[T : Eq] SparseArray::remove(
  self : SparseArray[T],
  idx : Int,
) -> SparseArray[T] where {
  proof_require: sparse_array_inv(self),
  proof_require: valid_idx(idx),
  proof_require: model(self).mem(idx),
  proof_ensure: result => sparse_array_inv(result),
  proof_ensure: result => model(result).eq(model(self).remove(idx)),
} {
  let old_data = self.data
  let old_len = old_data.length()
  if old_len == 1 {
    let result = { bitmap: zero_uint(), data: FixedArray::make(0, old_data[0]) }
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
      proof_reasoning: (
        #| Removing an entry first copies the untouched prefix `[0, pos)` into
        #| the smaller array. `remove_prefix_ok` records that the copied prefix is
        #| already identical to the old one.
        #|
        #| Each iteration copies one more prefix cell, so the processed range
        #| grows from `i` to `i + 1`.
        #|
        #| The measure `pos - i` decreases to zero, leaving the removal point
        #| ready for suffix compaction.
      ),
    }
    proof_assert remove_fill_ok(old_data, new_data, pos, pos)
    for i = pos; i < old_len - 1; {
      new_data[i] = old_data[i + 1]
      continue i + 1
    } where {
      proof_invariant: pos <= i,
      proof_invariant: i <= old_len - 1,
      proof_invariant: remove_fill_ok(old_data, new_data, pos, i),
      proof_reasoning: (
        #| This second loop closes the gap left by the removed entry. For the
        #| processed range `[pos, i)`, `remove_fill_ok` says every new slot `k`
        #| already contains the old value from `k + 1`.
        #|
        #| Each iteration extends that shifted suffix by one more element via the
        #| assignment `new_data[i] = old_data[i + 1]`.
        #|
        #| The measure `(old_len - 1) - i` decreases, and at exit the entire tail
        #| has been compacted left by one position, which is exactly
        #| `remove_data_ok`.
      ),
    }
    let result = { bitmap: bitmap_remove(self.bitmap, idx), data: new_data }
    proof_assert singleton_len_inv(self) == false
    proof_assert bitmap_remove_post(self.bitmap, idx, result.bitmap)
    proof_assert remove_data_ok(self, idx, result)
    proof_assert mem_value(self.bitmap, idx)
    proof_assert result.data.length() + 1 == self.data.length()
    proof_assert self.data.length() == count_value(self.bitmap, 0)
    proof_assert count_value(result.bitmap, 0) + 1 ==
      count_value(self.bitmap, 0)
    proof_assert result.data.length() == count_value(result.bitmap, 0)
    proof_assert rank_value(result.bitmap, idx, 0) ==
      rank_value(self.bitmap, idx, 0)
    proof_assert ∀ i : Int,
      valid_idx(i) && mem_value(result.bitmap, i) && i <= idx →
      rank_value(result.bitmap, i, 0) == rank_value(self.bitmap, i, 0)
    proof_assert ∀ i : Int,
      valid_idx(i) && mem_value(result.bitmap, i) && idx < i →
      rank_value(result.bitmap, i, 0) + 1 == rank_value(self.bitmap, i, 0)
    proof_assert ∀ i : Int,
      valid_idx(i) && mem_value(result.bitmap, i) && i == idx →
      0 <= rank_value(result.bitmap, i, 0) &&
      rank_value(result.bitmap, i, 0) < result.data.length()
    proof_assert ∀ i : Int,
      valid_idx(i) && mem_value(result.bitmap, i) && i != idx →
      0 <= rank_value(result.bitmap, i, 0) &&
      rank_value(result.bitmap, i, 0) < result.data.length()
    proof_assert sparse_array_inv(result)
    proof_assert ∀ j : Int,
      model(result).mem(j) == model(self).remove(idx).mem(j)
    proof_assert ∀ j : Int, model(result).mem(j) → valid_idx(j)
    proof_assert ∀ j : Int, model(result).mem(j) → j != idx
    proof_assert ∀ j : Int,
      model(result).mem(j) → model(result).find(j).equal(model(self).find(j))
    proof_assert ∀ j : Int,
      model(result).mem(j) →
      model(result).find(j).equal(model(self).remove(idx).find(j))
    proof_assert fmap_eq_hyp_local(model(result), model(self).remove(idx))
    proof_assert model(result).eq(model(self).remove(idx))
    proof_assert remove_post(self, idx, result)
    result
  }
}

///|
pub fn[T : Eq] SparseArray::length(
  self : SparseArray[T],
) -> Int where {
  proof_require: sparse_array_inv(self),
  proof_ensure: result => result == model(self).size(),
} {
  proof_assert length_post(self)
  self.data.length()
}
