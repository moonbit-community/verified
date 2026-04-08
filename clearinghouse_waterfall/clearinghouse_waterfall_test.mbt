///|
test "no shortfall leaves buffers untouched" {
  let house = make_house(120, 100, 10, 20, 30)
  let result = resolve_default(house)
  assert_eq(result.insurance_used, 0)
  assert_eq(result.junior_used, 0)
  assert_eq(result.senior_used, 0)
  assert_eq(result.socialized_loss, 0)
}

///|
test "insurance absorbs the whole shortfall when deep enough" {
  let house = make_house(80, 100, 30, 10, 10)
  let result = resolve_default(house)
  assert_eq(result.insurance_used, 20)
  assert_eq(result.junior_used, 0)
  assert_eq(result.senior_used, 0)
  assert_eq(result.socialized_loss, 0)
}

///|
test "losses cascade through all internal buffers before socialization" {
  let house = make_house(50, 120, 10, 15, 20)
  let result = resolve_default(house)
  assert_eq(result.insurance_used, 10)
  assert_eq(result.junior_used, 15)
  assert_eq(result.senior_used, 20)
  assert_eq(result.socialized_loss, 25)
}
