///|
test "empty bridge starts with no processed nonce" {
  let bridge = @bridge_custody.empty(100)
  assert_eq(@bridge_custody.nonce_used(bridge, 3), false)
}

///|
test "deposit preserves nonce history" {
  let bridge = @bridge_custody.empty(100)
  let funded = @bridge_custody.deposit(bridge, 40)
  assert_eq(funded.reserve, 140)
  assert_eq(@bridge_custody.nonce_used(funded, 3), false)
}

///|
test "withdraw consumes the nonce exactly once" {
  let bridge = @bridge_custody.empty(100)
  let spent = @bridge_custody.execute_withdraw(bridge, 3, 25)
  assert_eq(spent.reserve, 75)
  assert_eq(@bridge_custody.nonce_used(spent, 3), true)
  assert_eq(@bridge_custody.nonce_used(spent, 4), false)
}
