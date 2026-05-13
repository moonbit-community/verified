///|
test "threshold execution succeeds at quorum" {
  let votes = FixedArray::from_array([1, 0, 1, 1, 0][:])
  assert_eq(count_approvals(votes), 3)
  assert_eq(can_execute(votes, 3), true)
}

///|
test "threshold execution fails below quorum" {
  let votes = FixedArray::from_array([1, 0, 0, 1, 0][:])
  assert_eq(count_approvals(votes), 2)
  assert_eq(can_execute(votes, 3), false)
}
