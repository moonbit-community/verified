///|
test "auction clears at the first non-crossing level" {
  let bids = FixedArray::from_array([110, 105, 100, 90][:])
  let asks = FixedArray::from_array([80, 95, 101, 120][:])
  let result = clear_book(bids, asks)
  assert_eq(result.quantity, 2)
  assert_eq(result.price, 100)
}

///|
test "fully crossed books match every level" {
  let bids = FixedArray::from_array([110, 108, 105][:])
  let asks = FixedArray::from_array([80, 90, 100][:])
  let result = clear_book(bids, asks)
  assert_eq(result.quantity, 3)
  assert_eq(result.price, 102)
}

///|
test "empty crossing returns zero quantity and zero price" {
  let bids = FixedArray::from_array([90, 85, 80][:])
  let asks = FixedArray::from_array([95, 100, 110][:])
  let result = clear_book(bids, asks)
  assert_eq(result.quantity, 0)
  assert_eq(result.price, 0)
}
