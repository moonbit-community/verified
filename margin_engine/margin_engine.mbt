///|
pub struct Account {
  collateral : Int
  contracts : Int
  entry_price : Int
  funding_debt : Int
  maintenance_margin_bps : Int
} derive(Eq)

///|
pub fn open_account(
  collateral : Int,
  contracts : Int,
  entry_price : Int,
  funding_debt : Int,
  maintenance_margin_bps : Int,
) -> Account where {
  proof_require: 0 <= collateral,
  proof_require: 0 <= contracts,
  proof_require: 0 <= entry_price,
  proof_require: 0 <= funding_debt,
  proof_require: valid_margin_bps(maintenance_margin_bps),
  proof_require: (collateral - funding_debt) * 10000 >=
  contracts * entry_price * maintenance_margin_bps,
  proof_ensure: result => {
    open_account_post(
      collateral, contracts, entry_price, funding_debt, maintenance_margin_bps, result,
    )
  },
} {
  let result = {
    collateral,
    contracts,
    entry_price,
    funding_debt,
    maintenance_margin_bps,
  }
  proof_assert 0 <=
    (collateral - funding_debt + contracts * (entry_price - entry_price)) *
    10000 -
    contracts * entry_price * maintenance_margin_bps
  proof_assert healthy_at(result, entry_price)
  proof_assert open_account_post(
    collateral, contracts, entry_price, funding_debt, maintenance_margin_bps, result,
  )
  result
}

///|
pub fn equity_value(
  account : Account,
  mark : Int,
) -> Int where {
  proof_require: account_inv(account),
  proof_require: 0 <= mark,
  proof_ensure: result => equity_value_post(account, mark, result),
} {
  let result = account.collateral -
    account.funding_debt +
    account.contracts * (mark - account.entry_price)
  proof_assert equity_value_post(account, mark, result)
  result
}

///|
pub fn margin_buffer(
  account : Account,
  mark : Int,
) -> Int where {
  proof_require: account_inv(account),
  proof_require: 0 <= mark,
  proof_ensure: result => margin_buffer_post(account, mark, result),
} {
  let result = (
      account.collateral -
      account.funding_debt +
      account.contracts * (mark - account.entry_price)
    ) *
    10000 -
    account.contracts * mark * account.maintenance_margin_bps
  proof_assert margin_buffer_post(account, mark, result)
  result
}

///|
pub fn liquidation_price(
  account : Account,
) -> Int where {
  proof_require: account_inv(account),
  proof_ensure: result => liquidation_price_post(account, result),
} {
  let numerator = account.contracts * account.entry_price * 10000 +
    account.funding_debt * 10000 -
    account.collateral * 10000
  let result = if account.contracts == 0 || numerator <= 0 {
    0
  } else {
    let denominator = account.contracts *
      (10000 - account.maintenance_margin_bps)
    proof_assert 0 < 10000 - account.maintenance_margin_bps
    proof_assert 0 < denominator
    (numerator + denominator - 1) / denominator
  }
  proof_assert liquidation_price_post(account, result)
  result
}

///|
pub fn apply_funding(
  account : Account,
  amount : Int,
  mark : Int,
) -> Account where {
  proof_require: healthy_at(account, mark),
  proof_require: 0 <= amount,
  proof_require: 0 <=
  (
    account.collateral -
    account.funding_debt +
    account.contracts * (mark - account.entry_price)
  ) *
  10000 -
  account.contracts * mark * account.maintenance_margin_bps -
  amount * 10000,
  proof_ensure: result => apply_funding_post(account, amount, mark, result),
} {
  let result = {
    collateral: account.collateral,
    contracts: account.contracts,
    entry_price: account.entry_price,
    funding_debt: account.funding_debt + amount,
    maintenance_margin_bps: account.maintenance_margin_bps,
  }
  proof_assert (
      result.collateral -
      result.funding_debt +
      result.contracts * (mark - result.entry_price)
    ) *
    10000 -
    result.contracts * mark * result.maintenance_margin_bps ==
    (
      account.collateral -
      account.funding_debt +
      account.contracts * (mark - account.entry_price)
    ) *
    10000 -
    account.contracts * mark * account.maintenance_margin_bps -
    amount * 10000
  proof_assert apply_funding_post(account, amount, mark, result)
  result
}

///|
pub fn partial_close(
  account : Account,
  close_units : Int,
  mark : Int,
) -> Account where {
  proof_require: account_inv(account),
  proof_require: 0 <= mark,
  proof_require: 0 <= close_units,
  proof_require: close_units <= account.contracts,
  proof_require: 0 <=
  account.collateral + close_units * (mark - account.entry_price),
  proof_ensure: result => partial_close_post(account, close_units, mark, result),
} {
  let result = {
    collateral: account.collateral + close_units * (mark - account.entry_price),
    contracts: account.contracts - close_units,
    entry_price: account.entry_price,
    funding_debt: account.funding_debt,
    maintenance_margin_bps: account.maintenance_margin_bps,
  }
  proof_assert result.collateral -
    result.funding_debt +
    result.contracts * (mark - result.entry_price) ==
    account.collateral -
    account.funding_debt +
    account.contracts * (mark - account.entry_price)
  proof_assert (
      result.collateral -
      result.funding_debt +
      result.contracts * (mark - result.entry_price)
    ) *
    10000 -
    result.contracts * mark * result.maintenance_margin_bps ==
    (
      account.collateral -
      account.funding_debt +
      account.contracts * (mark - account.entry_price)
    ) *
    10000 -
    account.contracts * mark * account.maintenance_margin_bps +
    close_units * mark * account.maintenance_margin_bps
  proof_assert partial_close_post(account, close_units, mark, result)
  result
}

///|
pub fn min_close_to_restore(
  account : Account,
  mark : Int,
) -> Int where {
  proof_require: account_inv(account),
  proof_require: 0 < mark,
  proof_require: 0 <=
  account.collateral -
  account.funding_debt +
  account.contracts * (mark - account.entry_price),
  proof_ensure: result => min_close_to_restore_post(account, mark, result),
} {
  proof_assert 0 < account.maintenance_margin_bps
  let buffer = (
      account.collateral -
      account.funding_debt +
      account.contracts * (mark - account.entry_price)
    ) *
    10000 -
    account.contracts * mark * account.maintenance_margin_bps
  let denominator = mark * account.maintenance_margin_bps
  proof_assert 0 < denominator
  let result = if buffer >= 0 {
    let result = 0
    proof_assert result == 0
    proof_assert 0 <= result
    proof_assert result <= account.contracts
    proof_assert 0 <= buffer + result * mark * account.maintenance_margin_bps
    proof_assert min_close_frontier(account, mark, result)
    result
  } else {
    let numerator = -buffer
    proof_assert 0 < numerator
    proof_assert numerator <= account.contracts * denominator
    let result = (numerator + denominator - 1) / denominator
    proof_assert result == (numerator + denominator - 1) / denominator
    proof_assert 0 <= result
    proof_assert result * denominator <= numerator + denominator - 1
    proof_assert numerator + denominator - 1 < (result + 1) * denominator
    proof_assert numerator <= result * denominator
    proof_assert (result - 1) * denominator < numerator
    proof_assert result <= account.contracts
    proof_assert 0 <= buffer + result * mark * account.maintenance_margin_bps
    proof_assert min_close_frontier(account, mark, result)
    result
  }
  proof_assert min_close_to_restore_post(account, mark, result)
  result
}

///|
pub fn close_to_restore(
  account : Account,
  mark : Int,
) -> Account where {
  proof_require: account_inv(account),
  proof_require: 0 < mark,
  proof_require: 0 <=
  account.collateral -
  account.funding_debt +
  account.contracts * (mark - account.entry_price),
  proof_require: 0 <=
  account.collateral + account.contracts * (mark - account.entry_price),
  proof_ensure: result => close_to_restore_post(account, mark, result),
} {
  let close_units = min_close_to_restore(account, mark)
  proof_assert close_units <= account.contracts
  if 0 <= mark - account.entry_price {
    proof_assert 0 <= close_units * (mark - account.entry_price)
    proof_assert 0 <=
      account.collateral + close_units * (mark - account.entry_price)
  } else {
    proof_assert close_units * (mark - account.entry_price) >=
      account.contracts * (mark - account.entry_price)
    proof_assert 0 <=
      account.collateral + close_units * (mark - account.entry_price)
  }
  let result = partial_close(account, close_units, mark)
  proof_assert result.contracts + close_units == account.contracts
  proof_assert close_units == account.contracts - result.contracts
  proof_assert min_close_to_restore_post(
    account,
    mark,
    account.contracts - result.contracts,
  )
  proof_assert close_to_restore_post(account, mark, result)
  result
}

///|
pub fn is_liquidatable(
  account : Account,
  mark : Int,
) -> Bool where {
  proof_require: account_inv(account),
  proof_require: 0 <= mark,
  proof_ensure: result => liquidatable_post(account, mark, result),
} {
  let result = (
      account.collateral -
      account.funding_debt +
      account.contracts * (mark - account.entry_price)
    ) *
    10000 -
    account.contracts * mark * account.maintenance_margin_bps <
    0
  proof_assert liquidatable_post(account, mark, result)
  result
}
