///|
test "empty heap" {
  let h : @pairing_heap.Heap[Int] = @pairing_heap.empty()
  debug_inspect(@pairing_heap.find_min(h), content="None")
  debug_inspect(@pairing_heap.delete_min(h), content="None")
  debug_inspect(@pairing_heap.size(h), content="0")
}

///|
test "insert and min" {
  let h = @pairing_heap.insert(@pairing_heap.insert(@pairing_heap.insert(@pairing_heap.empty(), 5), 3), 7)
  debug_inspect(@pairing_heap.find_min(h), content="Some(3)")
  debug_inspect(@pairing_heap.size(h), content="3")
}

///|
test "duplicates survive delete" {
  let h = @pairing_heap.insert(@pairing_heap.insert(@pairing_heap.insert(@pairing_heap.empty(), 3), 3), 5)
  debug_inspect(@pairing_heap.find_min(h), content="Some(3)")
  let h1 = @pairing_heap.delete_min(h)
  debug_inspect(h1, content="Some(Node(3, Cons(Node(5, Nil, 1), Nil), 2))")
  debug_inspect(h1.map(fn(x) { @pairing_heap.find_min(x) }), content="Some(Some(3))")
}

///|
test "merge and persistence" {
  let h1 = @pairing_heap.insert(@pairing_heap.insert(@pairing_heap.empty(), 4), 1)
  let h2 = @pairing_heap.insert(@pairing_heap.insert(@pairing_heap.empty(), 3), 2)
  let merged = @pairing_heap.merge(h1, h2)
  debug_inspect(@pairing_heap.find_min(h1), content="Some(1)")
  debug_inspect(@pairing_heap.find_min(h2), content="Some(2)")
  debug_inspect(@pairing_heap.find_min(merged), content="Some(1)")
  debug_inspect(@pairing_heap.size(merged), content="4")
}
