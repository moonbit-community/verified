///|
test "empty heap" {
  let h : Heap[Int] = empty()
  inspect(find_min(h), content="None")
  inspect(delete_min(h), content="None")
  inspect(size(h), content="0")
}

///|
test "insert and min" {
  let h = insert(insert(insert(empty(), 5), 3), 7)
  inspect(find_min(h), content="Some(3)")
  inspect(size(h), content="3")
}

///|
test "duplicates survive delete" {
  let h = insert(insert(insert(empty(), 3), 3), 5)
  inspect(find_min(h), content="Some(3)")
  let h1 = delete_min(h)
  inspect(h1, content="Some(Node(3, Cons(Node(5, Nil, 1), Nil), 2))")
  inspect(h1.map(fn(x) { find_min(x) }), content="Some(Some(3))")
}

///|
test "merge and persistence" {
  let h1 = insert(insert(empty(), 4), 1)
  let h2 = insert(insert(empty(), 3), 2)
  let merged = merge(h1, h2)
  inspect(find_min(h1), content="Some(1)")
  inspect(find_min(h2), content="Some(2)")
  inspect(find_min(merged), content="Some(1)")
  inspect(size(merged), content="4")
}
