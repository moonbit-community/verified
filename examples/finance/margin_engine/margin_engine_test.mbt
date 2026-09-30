///|
test "liquidation price is the exact integer boundary" {
  let account = @margin_engine.open_account(50, 10, 10, 0, 500)
  assert_eq(@margin_engine.liquidation_price(account), 6)
  assert_eq(@margin_engine.is_liquidatable(account, 5), true)
  assert_eq(@margin_engine.is_liquidatable(account, 6), false)
}

///|
test "funding accrual consumes margin buffer exactly" {
  let account = @margin_engine.open_account(80, 5, 10, 0, 1000)
  let funded = @margin_engine.apply_funding(account, 3, 10)
  assert_eq(@margin_engine.equity_value(funded, 10), 77)
  assert_eq(@margin_engine.margin_buffer(funded, 10), 720_000)
}

///|
test "partial close preserves equity at the current mark" {
  let account = @margin_engine.open_account(50, 10, 10, 0, 9000)
  let closed = @margin_engine.partial_close(account, 4, 6)
  assert_eq(@margin_engine.equity_value(account, 6), 10)
  assert_eq(@margin_engine.equity_value(closed, 6), 10)
  assert_eq(@margin_engine.margin_buffer(closed, 6), -224_000)
}

///|
test "close_to_restore computes the minimal healthy deleveraging" {
  let account = @margin_engine.open_account(50, 10, 10, 0, 9000)
  assert_eq(@margin_engine.is_liquidatable(account, 6), true)
  assert_eq(@margin_engine.min_close_to_restore(account, 6), 9)
  let restored = @margin_engine.close_to_restore(account, 6)
  assert_eq(restored.contracts, 1)
  assert_eq(@margin_engine.is_liquidatable(restored, 6), false)
  assert_eq(@margin_engine.equity_value(restored, 6), 10)
}
