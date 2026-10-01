///|
test "leftist heap empty" {
  let h : @leftist_heap.Heap[Int] = @leftist_heap.empty()
  @debug.assert_eq(@leftist_heap.find_min(h), None)
  guard @leftist_heap.delete_min(h) is None else {
    fail("expected empty delete")
  }
  assert_eq(@leftist_heap.size(h), 0)
}

///|
test "leftist heap insertion order" {
  let h1 = @leftist_heap.insert(@leftist_heap.empty(), 5)
  let h2 = @leftist_heap.insert(h1, 3)
  let h3 = @leftist_heap.insert(h2, 7)
  @debug.assert_eq(@leftist_heap.find_min(h3), Some(3))
  assert_eq(@leftist_heap.size(h3), 3)
}

///|
test "leftist heap duplicates survive one delete" {
  let h1 = @leftist_heap.insert(@leftist_heap.empty(), 3)
  let h2 = @leftist_heap.insert(h1, 3)
  let h3 = @leftist_heap.insert(h2, 5)
  @debug.assert_eq(@leftist_heap.find_min(h3), Some(3))
  guard @leftist_heap.delete_min(h3) is Some(h4) else {
    fail("expected delete_min")
  }
  @debug.assert_eq(@leftist_heap.find_min(h4), Some(3))
  assert_eq(@leftist_heap.size(h4), 2)
}

///|
test "leftist heap persistence" {
  let h1 = @leftist_heap.insert(@leftist_heap.empty(), 10)
  let h2 = @leftist_heap.insert(h1, 2)
  @debug.assert_eq(@leftist_heap.find_min(h1), Some(10))
  @debug.assert_eq(@leftist_heap.find_min(h2), Some(2))
}

///|
test "leftist heap merge" {
  let a = @leftist_heap.insert(
    @leftist_heap.insert(@leftist_heap.empty(), 4),
    8,
  )
  let b = @leftist_heap.insert(
    @leftist_heap.insert(@leftist_heap.empty(), 1),
    6,
  )
  let merged = @leftist_heap.merge(a, b)
  @debug.assert_eq(@leftist_heap.find_min(merged), Some(1))
  assert_eq(@leftist_heap.size(merged), 4)
}
