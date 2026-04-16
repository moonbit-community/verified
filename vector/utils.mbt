///|
fn[T] immutable_set(
  arr : ReadOnlyArray[T],
  i : Int,
  v : T,
) -> ReadOnlyArray[T] where {
  proof_axiomatized: true,
  proof_require: 0 <= i,
  proof_require: i < @readonlyarray.model(arr).length(),
  proof_ensure: result => immutable_set_post(arr, i, v, result),
} {
  ReadOnlyArray::makei(arr.length(), fn(j) { if j == i { v } else { arr[j] } })
}

///|
fn[T] immutable_push(
  arr : ReadOnlyArray[T],
  value : T,
) -> ReadOnlyArray[T] where {
  proof_axiomatized: true,
  proof_ensure: result => immutable_push_post(arr, value, result),
} {
  let len = arr.length()
  ReadOnlyArray::makei(len + 1, fn(i) { if i < len { arr[i] } else { value } })
}

///|
fn[T] immutable_concat(
  left : ReadOnlyArray[T],
  right : ReadOnlyArray[T],
) -> ReadOnlyArray[T] {
  let left_len = left.length()
  let right_len = right.length()
  ReadOnlyArray::makei(left_len + right_len, fn(i) {
    if i < left_len {
      left[i]
    } else {
      right[i - left_len]
    }
  })
}

///|
fn[T] immutable_slice(
  arr : ReadOnlyArray[T],
  start : Int,
  stop : Int,
) -> ReadOnlyArray[T] where {
  proof_axiomatized: true,
  proof_require: 0 <= start,
  proof_require: start <= stop,
  proof_require: stop <= @readonlyarray.model(arr).length(),
  proof_ensure: result => immutable_slice_post(arr, start, stop, result),
} {
  let len = stop - start
  if len <= 0 {
    []
  } else {
    ReadOnlyArray::makei(len, fn(i) { arr[start + i] })
  }
}

///|
fn shr_as_uint(x : Int, y : Int) -> Int {
  (x.reinterpret_as_uint() >> y).reinterpret_as_int()
}

///|
fn radix_indexing(index : Int, shift : Int) -> Int {
  shr_as_uint(index, shift) & bitmask
}

///|
fn radix_subindex(index : Int, shift : Int) -> Int {
  index & ((1 << shift) - 1)
}

///|
fn get_branch_index(sizes : ReadOnlyArray[Int], index : Int) -> Int {
  let lo = for lo = 0, hi = sizes.length(); LINEAR_THRESHOLD < hi - lo; {
    let mid = (lo + hi) / 2
    if sizes[mid] <= index {
      continue mid, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  }
  for lo = lo; sizes[lo] <= index; {
    continue lo + 1
  } nobreak {
    lo
  }
}
