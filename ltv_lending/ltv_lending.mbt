///|
pub struct Position {
  collateral : Int
  debt : Int
  max_ltv_bps : Int
} derive(Eq)

///|
pub fn max_safe_debt(
  collateral : Int,
  max_ltv_bps : Int,
) -> Int where {
  proof_require: 0 <= collateral,
  proof_require: valid_bps(max_ltv_bps),
  proof_ensure: result => max_safe_debt_post(collateral, max_ltv_bps, result),
} {
  let result = collateral * max_ltv_bps / 10000
  proof_assert max_safe_debt_post(collateral, max_ltv_bps, result)
  result
}

///|
pub fn open(
  collateral : Int,
  debt : Int,
  max_ltv_bps : Int,
) -> Position where {
  proof_require: 0 <= collateral,
  proof_require: 0 <= debt,
  proof_require: valid_bps(max_ltv_bps),
  proof_require: debt * 10000 <= collateral * max_ltv_bps,
  proof_ensure: result => open_post(collateral, debt, max_ltv_bps, result),
} {
  let result = { collateral, debt, max_ltv_bps }
  proof_assert open_post(collateral, debt, max_ltv_bps, result)
  result
}

///|
pub fn borrow(
  position : Position,
  extra_debt : Int,
) -> Position where {
  proof_require: safe_position(position),
  proof_require: 0 <= extra_debt,
  proof_require: (position.debt + extra_debt) * 10000 <=
  position.collateral * position.max_ltv_bps,
  proof_ensure: result => borrow_post(position, extra_debt, result),
} {
  let result = {
    collateral: position.collateral,
    debt: position.debt + extra_debt,
    max_ltv_bps: position.max_ltv_bps,
  }
  proof_assert (position.debt + extra_debt) * 10000 ==
    position.debt * 10000 + extra_debt * 10000
  proof_assert result.collateral * result.max_ltv_bps - result.debt * 10000 ==
    position.collateral * position.max_ltv_bps -
    position.debt * 10000 -
    extra_debt * 10000
  proof_assert borrow_post(position, extra_debt, result)
  result
}

///|
pub fn repay(
  position : Position,
  payment : Int,
) -> Position where {
  proof_require: safe_position(position),
  proof_require: 0 <= payment,
  proof_require: payment <= position.debt,
  proof_ensure: result => repay_post(position, payment, result),
} {
  let result = {
    collateral: position.collateral,
    debt: position.debt - payment,
    max_ltv_bps: position.max_ltv_bps,
  }
  proof_assert (position.debt - payment) * 10000 ==
    position.debt * 10000 - payment * 10000
  proof_assert result.collateral * result.max_ltv_bps - result.debt * 10000 ==
    position.collateral * position.max_ltv_bps -
    position.debt * 10000 +
    payment * 10000
  proof_assert repay_post(position, payment, result)
  result
}

///|
pub fn add_collateral(
  position : Position,
  extra_collateral : Int,
) -> Position where {
  proof_require: safe_position(position),
  proof_require: 0 <= extra_collateral,
  proof_ensure: result => {
    add_collateral_post(position, extra_collateral, result)
  },
} {
  let result = {
    collateral: position.collateral + extra_collateral,
    debt: position.debt,
    max_ltv_bps: position.max_ltv_bps,
  }
  proof_assert (position.collateral + extra_collateral) * position.max_ltv_bps ==
    position.collateral * position.max_ltv_bps +
    extra_collateral * position.max_ltv_bps
  proof_assert result.collateral * result.max_ltv_bps - result.debt * 10000 ==
    position.collateral * position.max_ltv_bps -
    position.debt * 10000 +
    extra_collateral * position.max_ltv_bps
  proof_assert add_collateral_post(position, extra_collateral, result)
  result
}

///|
pub fn is_liquidatable(
  position : Position,
) -> Bool where {
  proof_require: position_inv(position),
  proof_ensure: result => liquidatable_post(position, result),
} {
  let result = position.collateral * position.max_ltv_bps <
    position.debt * 10000
  proof_assert liquidatable_post(position, result)
  result
}
