///|
test "empty bridge starts with no processed nonce" {
  let bridge = empty(100)
  assert_eq(nonce_used(bridge, 3), false)
}

///|
test "deposit preserves nonce history" {
  let bridge = empty(100)
  let funded = deposit(bridge, 40)
  assert_eq(funded.reserve, 140)
  assert_eq(nonce_used(funded, 3), false)
}

///|
test "withdraw consumes the nonce exactly once" {
  let bridge = empty(100)
  let spent = execute_withdraw(bridge, 3, 25)
  assert_eq(spent.reserve, 75)
  assert_eq(nonce_used(spent, 3), true)
  assert_eq(nonce_used(spent, 4), false)
}
