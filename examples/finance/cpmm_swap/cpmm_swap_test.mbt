///|
test "quote produces bounded output" {
  let pool = @cpmm_swap.make_pool(1_000, 1_000, 30)
  assert_eq(@cpmm_swap.quote_amount_out(pool, 100), 90)
}

///|
test "swap updates reserves conservatively" {
  let pool = @cpmm_swap.make_pool(1_000, 1_000, 30)
  let result = @cpmm_swap.swap_x_for_y(pool, 100)
  assert_eq(result.amount_out, 90)
  assert_eq(result.next_pool.reserve_in, 1_100)
  assert_eq(result.next_pool.reserve_out, 910)
}

///|
test "larger reserves produce smaller slippage" {
  let small = @cpmm_swap.make_pool(200, 200, 30)
  let deep = @cpmm_swap.make_pool(2_000, 2_000, 30)
  let small_out = @cpmm_swap.quote_amount_out(small, 100)
  let deep_out = @cpmm_swap.quote_amount_out(deep, 100)
  assert_eq(small_out, 66)
  assert_eq(deep_out, 94)
}
