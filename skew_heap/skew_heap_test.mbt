///|
test "skew heap empty" {
  let h : @skew_heap.Heap[Int] = @skew_heap.empty()
  @debug.assert_eq(@skew_heap.find_min(h), None)
  guard @skew_heap.delete_min(h) is None else { fail("expected empty delete") }
  assert_eq(@skew_heap.size(h), 0)
}

///|
test "skew heap insertion order" {
  let h = @skew_heap.from_array([5, 3, 7][:])
  @debug.assert_eq(@skew_heap.find_min(h), Some(3))
  assert_eq(@skew_heap.size(h), 3)
}

///|
test "skew heap duplicates survive one delete" {
  let h = @skew_heap.from_array([3, 3, 5][:])
  @debug.assert_eq(@skew_heap.find_min(h), Some(3))
  guard @skew_heap.delete_min(h) is Some(h1) else {
    fail("expected delete_min")
  }
  @debug.assert_eq(@skew_heap.find_min(h1), Some(3))
  assert_eq(@skew_heap.size(h1), 2)
}

///|
test "skew heap merge persistence" {
  let a = @skew_heap.from_array([7, 2, 5][:])
  let b = @skew_heap.from_array([4, 1, 9][:])
  let merged = @skew_heap.merge(a, b)
  @debug.assert_eq(@skew_heap.find_min(a), Some(2))
  @debug.assert_eq(@skew_heap.find_min(b), Some(1))
  @debug.assert_eq(@skew_heap.find_min(merged), Some(1))
  assert_eq(@skew_heap.size(merged), 6)
}
