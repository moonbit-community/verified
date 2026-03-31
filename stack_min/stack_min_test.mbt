///|
test "stack min empty" {
  let s = empty()
  assert_eq(min_value(s), None)
  guard pop(s) is None else { fail("expected empty pop") }
  assert_eq(size(s), 0)
}

///|
test "stack min push and pop" {
  let s1 = push(empty(), 5)
  let s2 = push(s1, 2)
  let s3 = push(s2, 7)
  assert_eq(min_value(s3), Some(2))
  guard pop(s3) is Some((7, s4)) else { fail("expected pop") }
  assert_eq(min_value(s4), Some(2))
}

///|
test "stack min duplicates" {
  let s = from_array([3, 3, 5][:])
  assert_eq(min_value(s), Some(3))
  guard pop(s) is Some((3, s1)) else { fail("expected pop") }
  assert_eq(min_value(s1), Some(3))
}
