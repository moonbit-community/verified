///|
pub struct Engine {
  collateral : Int
  debt : Int
  reserve : Int
  min_ratio_bps : Int
} derive(Eq)

///|
pub struct LiquidationResult {
  reserve_used : Int
  remaining_bad_debt : Int
  next_engine : Engine
} derive(Eq)

///|
#proof_pure
fn headroom(engine : Engine) -> Int {
  engine.collateral * 10000 - engine.debt * engine.min_ratio_bps
}

///|
#proof_pure
fn equity(engine : Engine) -> Int {
  engine.collateral + engine.reserve - engine.debt
}

///|
#proof_pure
fn deficit_after_collateral(engine : Engine) -> Int {
  if engine.debt <= engine.collateral {
    0
  } else {
    engine.debt - engine.collateral
  }
}

///|
#proof_pure
fn reserve_used_to_close(engine : Engine) -> Int {
  if deficit_after_collateral(engine) <= engine.reserve {
    deficit_after_collateral(engine)
  } else {
    engine.reserve
  }
}

///|
#proof_pure
fn uncovered_debt(engine : Engine) -> Int {
  deficit_after_collateral(engine) - reserve_used_to_close(engine)
}

///|
pub fn make_engine(
  collateral : Int,
  debt : Int,
  reserve : Int,
  min_ratio_bps : Int,
) -> Engine where {
  proof_require: 0 <= collateral,
  proof_require: 0 <= debt,
  proof_require: 0 <= reserve,
  proof_require: valid_ratio_bps(min_ratio_bps),
  proof_ensure: result => engine_inv(result),
} {
  let result = { collateral, debt, reserve, min_ratio_bps }
  proof_assert engine_inv(result)
  result
}

///|
pub fn open_engine(
  collateral : Int,
  debt : Int,
  reserve : Int,
  min_ratio_bps : Int,
) -> Engine where {
  proof_require: 0 <= collateral,
  proof_require: 0 <= debt,
  proof_require: 0 <= reserve,
  proof_require: valid_ratio_bps(min_ratio_bps),
  proof_require: debt * min_ratio_bps <= collateral * 10000,
  proof_ensure: result => open_engine_post(collateral, debt, reserve, min_ratio_bps, result),
} {
  let result = { collateral, debt, reserve, min_ratio_bps }
  proof_assert open_engine_post(collateral, debt, reserve, min_ratio_bps, result)
  result
}

///|
pub fn max_mintable(collateral : Int, min_ratio_bps : Int) -> Int where {
  proof_require: 0 <= collateral,
  proof_require: valid_ratio_bps(min_ratio_bps),
  proof_ensure: result => max_mintable_post(collateral, min_ratio_bps, result),
} {
  let result = collateral * 10000 / min_ratio_bps
  proof_assert max_mintable_post(collateral, min_ratio_bps, result)
  result
}

///|
pub fn safety_buffer(engine : Engine) -> Int where {
  proof_require: engine_inv(engine),
  proof_ensure: result => safety_buffer_post(engine, result),
} {
  let result = headroom(engine)
  proof_assert safety_buffer_post(engine, result)
  result
}

///|
pub fn equity_value(engine : Engine) -> Int where {
  proof_require: engine_inv(engine),
  proof_ensure: result => equity_value_post(engine, result),
} {
  let result = equity(engine)
  proof_assert equity_value_post(engine, result)
  result
}

///|
pub fn mint(engine : Engine, amount : Int) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_require:
    (engine.debt + amount) * engine.min_ratio_bps <= engine.collateral * 10000,
  proof_ensure: result => mint_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral,
    debt: engine.debt + amount,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert headroom(result) == headroom(engine) - amount * engine.min_ratio_bps
  proof_assert equity(result) == equity(engine) - amount
  proof_assert mint_post(engine, amount, result)
  result
}

///|
pub fn repay(engine : Engine, amount : Int) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_require: amount <= engine.debt,
  proof_ensure: result => repay_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral,
    debt: engine.debt - amount,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert headroom(result) == headroom(engine) + amount * engine.min_ratio_bps
  proof_assert equity(result) == equity(engine) + amount
  proof_assert repay_post(engine, amount, result)
  result
}

///|
pub fn add_collateral(engine : Engine, amount : Int) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_ensure: result => add_collateral_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral + amount,
    debt: engine.debt,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert headroom(result) == headroom(engine) + amount * 10000
  proof_assert equity(result) == equity(engine) + amount
  proof_assert add_collateral_post(engine, amount, result)
  result
}

///|
pub fn withdraw_collateral(engine : Engine, amount : Int) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_require:
    engine.debt * engine.min_ratio_bps <=
    (engine.collateral - amount) * 10000,
  proof_ensure: result => withdraw_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral - amount,
    debt: engine.debt,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert headroom(result) == headroom(engine) - amount * 10000
  proof_assert equity(result) == equity(engine) - amount
  proof_assert withdraw_post(engine, amount, result)
  result
}

///|
pub fn add_reserve(engine : Engine, amount : Int) -> Engine where {
  proof_require: engine_inv(engine),
  proof_require: 0 <= amount,
  proof_ensure: result => add_reserve_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral,
    debt: engine.debt,
    reserve: engine.reserve + amount,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert headroom(result) == headroom(engine)
  proof_assert equity(result) == equity(engine) + amount
  proof_assert add_reserve_post(engine, amount, result)
  result
}

///|
pub fn is_liquidatable(engine : Engine) -> Bool where {
  proof_require: engine_inv(engine),
  proof_ensure: result => liquidatable_post(engine, result),
} {
  let result = headroom(engine) < 0
  proof_assert liquidatable_post(engine, result)
  result
}

///|
pub fn liquidate_all(engine : Engine) -> LiquidationResult where {
  proof_require: engine_inv(engine),
  proof_require: liquidatable(engine),
  proof_ensure: result => liquidate_all_post(engine, result),
} {
  let reserve_used = if deficit_after_collateral(engine) <= engine.reserve {
    deficit_after_collateral(engine)
  } else {
    engine.reserve
  }
  let remaining_bad_debt = deficit_after_collateral(engine) - reserve_used
  let next_engine = {
    collateral: 0,
    debt: remaining_bad_debt,
    reserve: engine.reserve - reserve_used,
    min_ratio_bps: engine.min_ratio_bps,
  }
  let result = { reserve_used, remaining_bad_debt, next_engine }
  proof_assert reserve_used == reserve_used_to_close(engine)
  proof_assert remaining_bad_debt == uncovered_debt(engine)
  proof_assert liquidate_all_post(engine, result)
  result
}
