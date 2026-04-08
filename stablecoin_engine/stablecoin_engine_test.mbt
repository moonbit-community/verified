///|
test "max mintable is the exact floor of the collateral limit" {
  assert_eq(max_mintable(150, 15000), 100)
  assert_eq(max_mintable(151, 15000), 100)
}

///|
test "mint to the edge consumes the whole safety buffer" {
  let engine = open_engine(150, 60, 20, 15000)
  let minted = mint(engine, 40)
  assert_eq(minted.debt, 100)
  assert_eq(safety_buffer(minted), 0)
  assert_eq(equity_value(minted), 70)
}

///|
test "repay and withdraw track headroom exactly" {
  let engine = open_engine(180, 80, 15, 15000)
  let repaid = repay(engine, 20)
  let withdrawn = withdraw_collateral(repaid, 20)
  assert_eq(repaid.debt, 60)
  assert_eq(safety_buffer(repaid), 900_000)
  assert_eq(withdrawn.collateral, 160)
  assert_eq(safety_buffer(withdrawn), 700_000)
}

///|
test "full liquidation of an unsafe but solvent engine leaves no bad debt" {
  let engine = make_engine(120, 100, 10, 15000)
  assert_eq(is_liquidatable(engine), true)
  let result = liquidate_all(engine)
  assert_eq(result.reserve_used, 0)
  assert_eq(result.remaining_bad_debt, 0)
  assert_eq(result.next_engine.reserve, 10)
}

///|
test "full liquidation computes exact residual bad debt after reserve is exhausted" {
  let engine = make_engine(60, 100, 25, 15000)
  assert_eq(is_liquidatable(engine), true)
  let result = liquidate_all(engine)
  assert_eq(result.reserve_used, 25)
  assert_eq(result.remaining_bad_debt, 15)
  assert_eq(result.next_engine.reserve, 0)
}
