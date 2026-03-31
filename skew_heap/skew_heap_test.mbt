///|
test "skew heap empty" {
  let h = empty()
  assert_eq(find_min(h), None)
  guard delete_min(h) is None else { fail("expected empty delete") }
  assert_eq(size(h), 0)
}

///|
test "skew heap insertion order" {
  let h = from_array([5, 3, 7][:])
  assert_eq(find_min(h), Some(3))
  assert_eq(size(h), 3)
}

///|
test "skew heap duplicates survive one delete" {
  let h = from_array([3, 3, 5][:])
  assert_eq(find_min(h), Some(3))
  guard delete_min(h) is Some(h1) else { fail("expected delete_min") }
  assert_eq(find_min(h1), Some(3))
  assert_eq(size(h1), 2)
}

///|
test "skew heap merge persistence" {
  let a = from_array([7, 2, 5][:])
  let b = from_array([4, 1, 9][:])
  let merged = merge(a, b)
  assert_eq(find_min(a), Some(2))
  assert_eq(find_min(b), Some(1))
  assert_eq(find_min(merged), Some(1))
  assert_eq(size(merged), 6)
}
