///|
pub struct House {
  collateral : Int
  liability : Int
  insurance : Int
  junior : Int
  senior : Int
} derive(Eq)

///|
pub struct Resolution {
  insurance_used : Int
  junior_used : Int
  senior_used : Int
  socialized_loss : Int
  next_house : House
} derive(Eq)

///|
#proof_pure
fn shortfall(house : House) -> Int {
  if house.liability <= house.collateral {
    0
  } else {
    house.liability - house.collateral
  }
}

///|
#proof_pure
fn insurance_used_to_cover(house : House) -> Int {
  if shortfall(house) <= house.insurance {
    shortfall(house)
  } else {
    house.insurance
  }
}

///|
#proof_pure
fn remaining_after_insurance(house : House) -> Int {
  shortfall(house) - insurance_used_to_cover(house)
}

///|
#proof_pure
fn junior_used_to_cover(house : House) -> Int {
  if remaining_after_insurance(house) <= house.junior {
    remaining_after_insurance(house)
  } else {
    house.junior
  }
}

///|
#proof_pure
fn remaining_after_junior(house : House) -> Int {
  remaining_after_insurance(house) - junior_used_to_cover(house)
}

///|
#proof_pure
fn senior_used_to_cover(house : House) -> Int {
  if remaining_after_junior(house) <= house.senior {
    remaining_after_junior(house)
  } else {
    house.senior
  }
}

///|
#proof_pure
fn socialized_tail_loss(house : House) -> Int {
  remaining_after_junior(house) - senior_used_to_cover(house)
}

///|
pub fn make_house(
  collateral : Int,
  liability : Int,
  insurance : Int,
  junior : Int,
  senior : Int,
) -> House where {
  proof_require: 0 <= collateral,
  proof_require: 0 <= liability,
  proof_require: 0 <= insurance,
  proof_require: 0 <= junior,
  proof_require: 0 <= senior,
  proof_ensure: result => house_inv(result),
} {
  let result = { collateral, liability, insurance, junior, senior }
  proof_assert house_inv(result)
  result
}

///|
pub fn total_buffer(
  house : House,
) -> Int where {
  proof_require: house_inv(house),
  proof_ensure: result => total_buffer_post(house, result),
} {
  let result = house.insurance + house.junior + house.senior
  proof_assert total_buffer_post(house, result)
  result
}

///|
pub fn can_fully_absorb(
  house : House,
) -> Bool where {
  proof_require: house_inv(house),
  proof_ensure: result => can_fully_absorb_post(house, result),
} {
  let result = shortfall(house) <= house.insurance + house.junior + house.senior
  proof_assert can_fully_absorb_post(house, result)
  result
}

///|
pub fn add_insurance(
  house : House,
  amount : Int,
) -> House where {
  proof_require: house_inv(house),
  proof_require: 0 <= amount,
  proof_ensure: result => add_insurance_post(house, amount, result),
} {
  let result = {
    collateral: house.collateral,
    liability: house.liability,
    insurance: house.insurance + amount,
    junior: house.junior,
    senior: house.senior,
  }
  proof_assert add_insurance_post(house, amount, result)
  result
}

///|
pub fn resolve_default(
  house : House,
) -> Resolution where {
  proof_require: house_inv(house),
  proof_ensure: result => resolve_default_post(house, result),
} {
  let insurance_used = if shortfall(house) <= house.insurance {
    shortfall(house)
  } else {
    house.insurance
  }
  let remaining_after_insurance = shortfall(house) - insurance_used
  let junior_used = if remaining_after_insurance <= house.junior {
    remaining_after_insurance
  } else {
    house.junior
  }
  let remaining_after_junior = remaining_after_insurance - junior_used
  let senior_used = if remaining_after_junior <= house.senior {
    remaining_after_junior
  } else {
    house.senior
  }
  let socialized_loss = remaining_after_junior - senior_used
  let next_house = {
    collateral: 0,
    liability: 0,
    insurance: house.insurance - insurance_used,
    junior: house.junior - junior_used,
    senior: house.senior - senior_used,
  }
  let result = {
    insurance_used,
    junior_used,
    senior_used,
    socialized_loss,
    next_house,
  }
  proof_assert insurance_used == insurance_used_to_cover(house)
  proof_assert junior_used == junior_used_to_cover(house)
  proof_assert senior_used == senior_used_to_cover(house)
  proof_assert socialized_loss == socialized_tail_loss(house)
  proof_assert resolve_default_post(house, result)
  result
}
