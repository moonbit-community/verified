///|
test "stack min empty" {
  let s = @stack_min.empty()
  @debug.assert_eq(@stack_min.min_value(s), None)
  guard @stack_min.pop(s) is None else { fail("expected empty pop") }
  assert_eq(@stack_min.size(s), 0)
}

///|
test "stack min push and pop" {
  let s1 = @stack_min.push(@stack_min.empty(), 5)
  let s2 = @stack_min.push(s1, 2)
  let s3 = @stack_min.push(s2, 7)
  @debug.assert_eq(@stack_min.min_value(s3), Some(2))
  guard @stack_min.pop(s3) is Some((7, s4)) else { fail("expected pop") }
  @debug.assert_eq(@stack_min.min_value(s4), Some(2))
}

///|
test "stack min duplicates" {
  let s = @stack_min.from_array([3, 3, 5][:])
  @debug.assert_eq(@stack_min.min_value(s), Some(3))
  guard @stack_min.pop(s) is Some((3, s1)) else { fail("expected pop") }
  @debug.assert_eq(@stack_min.min_value(s1), Some(3))
}
