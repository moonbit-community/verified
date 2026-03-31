///|
test "leftist heap empty" {
  let h = empty()
  assert_eq(find_min(h), None)
  guard delete_min(h) is None else { fail("expected empty delete") }
  assert_eq(size(h), 0)
}

///|
test "leftist heap insertion order" {
  let h1 = insert(empty(), 5)
  let h2 = insert(h1, 3)
  let h3 = insert(h2, 7)
  assert_eq(find_min(h3), Some(3))
  assert_eq(size(h3), 3)
}

///|
test "leftist heap duplicates survive one delete" {
  let h1 = insert(empty(), 3)
  let h2 = insert(h1, 3)
  let h3 = insert(h2, 5)
  assert_eq(find_min(h3), Some(3))
  guard delete_min(h3) is Some(h4) else { fail("expected delete_min") }
  assert_eq(find_min(h4), Some(3))
  assert_eq(size(h4), 2)
}

///|
test "leftist heap persistence" {
  let h1 = insert(empty(), 10)
  let h2 = insert(h1, 2)
  assert_eq(find_min(h1), Some(10))
  assert_eq(find_min(h2), Some(2))
}

///|
test "leftist heap merge" {
  let a = insert(insert(empty(), 4), 8)
  let b = insert(insert(empty(), 1), 6)
  let merged = merge(a, b)
  assert_eq(find_min(merged), Some(1))
  assert_eq(size(merged), 4)
}
