///|
test "max safe debt uses ltv floor" {
  assert_eq(@ltv_lending.max_safe_debt(150, 8000), 120)
  assert_eq(@ltv_lending.max_safe_debt(101, 7500), 75)
}

///|
test "borrow stays solvent at the edge" {
  let position = @ltv_lending.open(150, 60, 8000)
  let result = @ltv_lending.borrow(position, 60)
  assert_eq(result.collateral, 150)
  assert_eq(result.debt, 120)
  assert_eq(@ltv_lending.is_liquidatable(result), false)
}

///|
test "repay and add collateral rebuild buffer" {
  let position = @ltv_lending.open(150, 100, 8000)
  let repaid = @ltv_lending.repay(position, 25)
  let improved = @ltv_lending.add_collateral(repaid, 10)
  assert_eq(repaid.debt, 75)
  assert_eq(improved.collateral, 160)
  assert_eq(@ltv_lending.is_liquidatable(improved), false)
}
