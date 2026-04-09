///|
test "liquidation price is the exact integer boundary" {
  let account = open_account(50, 10, 10, 0, 500)
  assert_eq(liquidation_price(account), 6)
  assert_eq(is_liquidatable(account, 5), true)
  assert_eq(is_liquidatable(account, 6), false)
}

///|
test "funding accrual consumes margin buffer exactly" {
  let account = open_account(80, 5, 10, 0, 1000)
  let funded = apply_funding(account, 3, 10)
  assert_eq(equity_value(funded, 10), 77)
  assert_eq(margin_buffer(funded, 10), 720_000)
}

///|
test "partial close preserves equity at the current mark" {
  let account = open_account(50, 10, 10, 0, 9000)
  let closed = partial_close(account, 4, 6)
  assert_eq(equity_value(account, 6), 10)
  assert_eq(equity_value(closed, 6), 10)
  assert_eq(margin_buffer(closed, 6), -224_000)
}

///|
test "close_to_restore computes the minimal healthy deleveraging" {
  let account = open_account(50, 10, 10, 0, 9000)
  assert_eq(is_liquidatable(account, 6), true)
  assert_eq(min_close_to_restore(account, 6), 9)
  let restored = close_to_restore(account, 6)
  assert_eq(restored.contracts, 1)
  assert_eq(is_liquidatable(restored, 6), false)
  assert_eq(equity_value(restored, 6), 10)
}
