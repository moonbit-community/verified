///|
pub struct Pool {
  reserve_in : Int
  reserve_out : Int
  fee_bps : Int
} derive(Eq)

///|
pub struct SwapResult {
  amount_out : Int
  next_pool : Pool
} derive(Eq)

///|
#proof_pure
fn fee_multiplier(fee_bps : Int) -> Int {
  10000 - fee_bps
}

///|
pub fn make_pool(reserve_in : Int, reserve_out : Int, fee_bps : Int) -> Pool {
  { reserve_in, reserve_out, fee_bps }
}

///|
pub fn quote_amount_out(pool : Pool, amount_in : Int) -> Int where {
  proof_require: pool_inv(pool),
  proof_require: 0 < amount_in,
  proof_ensure: result => quote_post(pool, amount_in, result),
} {
  let effective_in = amount_in * fee_multiplier(pool.fee_bps)
  let numerator = effective_in * pool.reserve_out
  let denominator = pool.reserve_in * 10000 + effective_in
  let result = numerator / denominator
  proof_assert 0 < fee_multiplier(pool.fee_bps)
  proof_assert 0 < denominator
  proof_assert result * denominator <= numerator
  proof_assert numerator < (result + 1) * denominator
  proof_assert numerator < denominator * pool.reserve_out
  proof_assert result < pool.reserve_out
  proof_assert quote_post(pool, amount_in, result)
  result
}

///|
pub fn swap_x_for_y(pool : Pool, amount_in : Int) -> SwapResult where {
  proof_require: pool_inv(pool),
  proof_require: 0 < amount_in,
  proof_ensure: result => swap_post(pool, amount_in, result),
} {
  let amount_out = quote_amount_out(pool, amount_in)
  let next_pool = {
    reserve_in: pool.reserve_in + amount_in,
    reserve_out: pool.reserve_out - amount_out,
    fee_bps: pool.fee_bps,
  }
  let fee = fee_multiplier(pool.fee_bps)
  proof_assert 0 < fee
  proof_assert fee <= 10000
  proof_assert fee * (pool.reserve_in + amount_in) <= pool.reserve_in * 10000 + amount_in * fee
  proof_assert amount_out * fee * (pool.reserve_in + amount_in) <= amount_in * fee * pool.reserve_out
  proof_assert amount_out * (pool.reserve_in + amount_in) <= amount_in * pool.reserve_out
  proof_assert
    next_pool.reserve_in * next_pool.reserve_out ==
    pool.reserve_in * pool.reserve_out +
    amount_in * pool.reserve_out -
    amount_out * (pool.reserve_in + amount_in)
  proof_assert next_pool.reserve_in * next_pool.reserve_out >= pool.reserve_in * pool.reserve_out
  let result = { amount_out, next_pool }
  proof_assert swap_post(pool, amount_in, result)
  result
}
