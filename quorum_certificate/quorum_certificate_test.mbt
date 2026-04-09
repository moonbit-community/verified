///|
fn bitmap_of_five(a : Int, b : Int, c : Int, d : Int, e : Int) -> UInt {
  (1U << a) | (1U << b) | (1U << c) | (1U << d) | (1U << e)
}

///|
test "signer_count and shared_count compute quorum sizes exactly" {
  let left = bitmap_of_five(0, 1, 2, 3, 4)
  let right = bitmap_of_five(2, 3, 4, 5, 6)
  assert_eq(signer_count(left, 7), 5)
  assert_eq(signer_count(right, 7), 5)
  assert_eq(shared_count(left, right, 7), 3)
  assert_eq(has_quorum(left, 7, 2), true)
  assert_eq(has_quorum(right, 7, 2), true)
}

///|
test "conflicting quorum certificates force slashable overlap" {
  let left = make_qc(10, 9, bitmap_of_five(0, 1, 2, 3, 4))
  let right = make_qc(11, 9, bitmap_of_five(2, 3, 4, 5, 6))
  assert_eq(conflicting(left, right), true)
  assert_eq(slashable_overlap(left, right, 7, 2), 3)
  assert_eq(slashable(left, right, 7, 2), true)
}

///|
test "same block is not slashable even with quorum overlap" {
  let left = make_qc(10, 9, bitmap_of_five(0, 1, 2, 3, 4))
  let right = make_qc(10, 9, bitmap_of_five(2, 3, 4, 5, 6))
  assert_eq(conflicting(left, right), false)
  assert_eq(slashable(left, right, 7, 2), false)
}
