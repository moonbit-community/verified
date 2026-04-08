///|
test "find first breach in portfolio" {
  let exposures = FixedArray::from_array([50, 70, 125, 90][:])
  let limits = FixedArray::from_array([80, 80, 120, 100][:])
  assert_eq(first_breach(exposures, limits), Some(2))
}

///|
test "no breach when portfolio stays inside envelope" {
  let exposures = FixedArray::from_array([50, 70, 115, 90][:])
  let limits = FixedArray::from_array([80, 80, 120, 100][:])
  assert_eq(first_breach(exposures, limits), None)
}
