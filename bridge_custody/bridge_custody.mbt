///|
using @fset {type Fset}

///|
pub struct Bridge {
  reserve : Int
  used_nonces : UInt
} derive(Eq)

///|
fn nonce_mem(bitmap : UInt, nonce : Int) -> Bool where {
  proof_require: @bitmap32.valid_idx(nonce),
  proof_ensure: result => result == @bitmap32.mem_value(bitmap, nonce),
} {
  let shifted = @bitmap32.uint_lsr(bitmap, nonce)
  let result = @bitmap32.uint_bit0(shifted)
  proof_assert result == @bv32.uint_to_bv(shifted).nth(0)
  proof_assert result == @bitmap32.mem_value(bitmap, nonce)
  result
}

///|
pub fn empty(reserve : Int) -> Bridge where {
  proof_require: 0 <= reserve,
  proof_ensure: result => empty_post(reserve, result),
} {
  let used_nonces = @bitmap32.zero_uint()
  let result = { reserve, used_nonces }
  proof_assert bridge_inv(result)
  proof_assert model(result).eq(@fset.fset_empty())
  proof_assert empty_post(reserve, result)
  result
}

///|
pub fn deposit(bridge : Bridge, amount : Int) -> Bridge where {
  proof_require: bridge_inv(bridge),
  proof_require: 0 <= amount,
  proof_ensure: result => deposit_post(bridge, amount, result),
} {
  let result = {
    reserve: bridge.reserve + amount,
    used_nonces: bridge.used_nonces,
  }
  proof_assert deposit_post(bridge, amount, result)
  result
}

///|
pub fn nonce_used(bridge : Bridge, nonce : Int) -> Bool where {
  proof_require: bridge_inv(bridge),
  proof_require: @bitmap32.valid_idx(nonce),
  proof_ensure: result => nonce_used_post(bridge, nonce, result),
} {
  let result = nonce_mem(bridge.used_nonces, nonce)
  proof_assert nonce_used_post(bridge, nonce, result)
  result
}

///|
pub fn execute_withdraw(
  bridge : Bridge,
  nonce : Int,
  amount : Int,
) -> Bridge where {
  proof_require: bridge_inv(bridge),
  proof_require: @bitmap32.valid_idx(nonce),
  proof_require: model(bridge).mem(nonce) == false,
  proof_require: 0 <= amount,
  proof_require: amount <= bridge.reserve,
  proof_ensure: result => execute_withdraw_post(bridge, nonce, amount, result),
} {
  let used_nonces = @bitmap32.bitmap_add(bridge.used_nonces, nonce)
  let result = { reserve: bridge.reserve - amount, used_nonces }
  proof_assert execute_withdraw_post(bridge, nonce, amount, result)
  result
}
