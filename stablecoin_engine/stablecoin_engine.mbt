///|
/// The aggregate state of a stablecoin vault. `collateral` is the backing the
/// user has posted, `debt` is the stablecoin supply they owe against it, and
/// `reserve` is the protocol-owned buffer that absorbs losses when a vault goes
/// under water. `min_ratio_bps` encodes the minimum collateralization ratio in
/// basis points, so `10000` means 100% and `15000` means 150%.
///
/// Everything is kept in integer arithmetic by scaling every ratio comparison
/// by `10000`. That scaling is the reason `headroom` and the proof obligations
/// read as `collateral * 10000` vs `debt * min_ratio_bps` rather than a ratio
/// test — it keeps the whole module decidable over integers without giving up
/// exactness at the liquidation boundary.
///
/// The base invariant `engine_inv` (see `stablecoin_engine.mbtp`) keeps all
/// three balances non-negative and requires `min_ratio_bps` to lie in the
/// valid `[10000, 30000]` window. Healthier states layer on top:
/// `healthy` additionally requires `headroom(engine) >= 0`, and
/// `liquidatable` is the strict negation of healthy on top of `engine_inv`.
pub struct Engine {
  collateral : Int
  debt : Int
  reserve : Int
  min_ratio_bps : Int
} derive(Eq)

///|
/// The result of unwinding an under-collateralized vault with `liquidate_all`.
/// `reserve_used` is how much of the protocol reserve was consumed to cover
/// the shortfall, `remaining_bad_debt` is the residual debt the protocol has
/// to absorb if the reserve was not enough, and `next_engine` is the engine
/// state after the liquidation settles (zero collateral, reserve and debt
/// updated accordingly).
///
/// The post-condition `liquidate_all_post` enforces the disjunction
/// `next_engine.reserve == 0 || next_engine.debt == 0`: either the reserve
/// fully absorbed the loss and no debt remains, or the reserve was drained to
/// zero and whatever is left lives on as bad debt.
pub struct LiquidationResult {
  reserve_used : Int
  remaining_bad_debt : Int
  next_engine : Engine
} derive(Eq)

///|
/// The amount of debt that cannot be covered by seizing the full collateral
/// alone. Zero whenever the collateral is at least the debt. This is the
/// quantity that a liquidation has to cover out of the reserve (and possibly
/// leave behind as bad debt).
#proof_pure
fn deficit_after_collateral(engine : Engine) -> Int {
  if engine.debt <= engine.collateral {
    0
  } else {
    engine.debt - engine.collateral
  }
}

///|
/// How much of the reserve actually gets consumed by a full liquidation:
/// the deficit if the reserve can cover it, otherwise the entire reserve.
/// Equivalently `min(deficit_after_collateral, reserve)`, written as an
/// explicit `if` so the proof obligations stay first-order.
#proof_pure
fn reserve_used_to_close(engine : Engine) -> Int {
  if deficit_after_collateral(engine) <= engine.reserve {
    deficit_after_collateral(engine)
  } else {
    engine.reserve
  }
}

///|
/// The residual bad debt left over after seizing collateral and draining as
/// much of the reserve as needed. Always non-negative, and by construction is
/// zero in the case where the reserve covered the deficit completely. This is
/// where the `reserve == 0 || debt == 0` disjunction in
/// `liquidate_all_post` comes from: at least one of the two sides must have
/// hit zero before the computation stopped.
#proof_pure
fn uncovered_debt(engine : Engine) -> Int {
  deficit_after_collateral(engine) - reserve_used_to_close(engine)
}

///|
/// The permissive constructor. It only asks for the base balance invariant
/// (non-negative values and a valid ratio) and crucially does *not* require
/// the resulting engine to be healthy. That makes it the right tool for
/// setting up liquidation test cases and for the protocol to reconstruct an
/// engine state after an external event has already pushed it under water.
/// For the common "open a fresh position" case, use `open_engine` instead,
/// which additionally enforces the healthy-at-creation ratio.
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
/// Factory for fresh positions. On top of the `make_engine` preconditions it
/// enforces `debt * min_ratio_bps <= collateral * 10000`, which is exactly
/// `headroom >= 0` in integer form. This is the single entry point that
/// guarantees `healthy(result)` from day one — every other mutation in the
/// module takes `healthy` as a precondition, so `open_engine` is how callers
/// step into the healthy-state chain to begin with.
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
  proof_ensure: result => {
    open_engine_post(collateral, debt, reserve, min_ratio_bps, result)
  },
} {
  let result = { collateral, debt, reserve, min_ratio_bps }
  proof_assert 0 <= collateral * 10000 - debt * min_ratio_bps
  proof_assert healthy(result)
  proof_assert open_engine_post(
    collateral, debt, reserve, min_ratio_bps, result,
  )
  result
}

///|
/// The largest integer debt that can be backed by the given collateral at the
/// given ratio. It is the exact integer floor of `collateral * 10000 /
/// min_ratio_bps`, which the post-condition pins down with the two
/// inequalities `result * min_ratio_bps <= collateral * 10000` and
/// `collateral * 10000 < (result + 1) * min_ratio_bps`. Those together
/// characterize the floor uniquely, so callers can use this function as the
/// canonical limit when sizing a new mint.
pub fn max_mintable(
  collateral : Int,
  min_ratio_bps : Int,
) -> Int where {
  proof_require: 0 <= collateral,
  proof_require: valid_ratio_bps(min_ratio_bps),
  proof_ensure: result => max_mintable_post(collateral, min_ratio_bps, result),
} {
  let result = collateral * 10000 / min_ratio_bps
  proof_assert max_mintable_post(collateral, min_ratio_bps, result)
  result
}

///|
/// Exposes the internal `headroom` as public, read-only telemetry. The raw
/// scaled value is useful because it is what every other post-condition in
/// this module talks about: a caller that tracks this across a sequence of
/// operations can reconstruct the exact effect of each action without having
/// to redo the ratio arithmetic.
pub fn safety_buffer(
  engine : Engine,
) -> Int where {
  proof_require: engine_inv(engine),
  proof_ensure: result => safety_buffer_post(engine, result),
} {
  let result = engine.collateral * 10000 - engine.debt * engine.min_ratio_bps
  proof_assert safety_buffer_post(engine, result)
  result
}

///|
/// Public view onto `equity`: `collateral + reserve - debt`. This is the
/// quantity that stakeholders would recover if every debt position were
/// settled at par. Unlike `safety_buffer` it does not depend on the ratio, so
/// it is the right quantity to watch for "does the protocol have enough total
/// resources" as opposed to "is this particular vault safe right now".
pub fn equity_value(
  engine : Engine,
) -> Int where {
  proof_require: engine_inv(engine),
  proof_ensure: result => equity_value_post(engine, result),
} {
  let result = engine.collateral + engine.reserve - engine.debt
  proof_assert equity_value_post(engine, result)
  result
}

///|
/// Grow the debt of a healthy engine by `amount`. The precondition
/// `(debt + amount) * min_ratio_bps <= collateral * 10000` is the
/// integer-form statement that the post-state is still at or above the
/// minimum ratio: it is exactly "post-state headroom is non-negative" after
/// rearranging. Collateral, reserve, and the ratio are untouched, so the only
/// book-keeping facts the proof needs are the two linear identities the body
/// asserts — headroom drops by `amount * min_ratio_bps` (the ratio-weighted
/// cost of each new debt unit) and equity drops by `amount` (one new
/// liability is created with no matching asset).
pub fn mint(
  engine : Engine,
  amount : Int,
) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_require: (engine.debt + amount) * engine.min_ratio_bps <=
  engine.collateral * 10000,
  proof_ensure: result => mint_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral,
    debt: engine.debt + amount,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert (engine.debt + amount) * engine.min_ratio_bps ==
    engine.debt * engine.min_ratio_bps + amount * engine.min_ratio_bps
  proof_assert result.collateral * 10000 - result.debt * result.min_ratio_bps ==
    engine.collateral * 10000 -
    engine.debt * engine.min_ratio_bps -
    amount * engine.min_ratio_bps
  proof_assert result.collateral + result.reserve - result.debt ==
    engine.collateral + engine.reserve - engine.debt - amount
  proof_assert mint_post(engine, amount, result)
  result
}

///|
/// The exact inverse of `mint`: shrink the debt by `amount`, with the payment
/// capped at the current debt so the field cannot go negative. Headroom grows
/// by `amount * min_ratio_bps` and equity grows by `amount`, which mirrors the
/// mint equations with opposite signs. No ratio precondition is needed
/// because repaying debt can only push the engine further above the minimum
/// ratio, never below it.
pub fn repay(
  engine : Engine,
  amount : Int,
) -> Engine where {
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
  proof_assert (engine.debt - amount) * engine.min_ratio_bps ==
    engine.debt * engine.min_ratio_bps - amount * engine.min_ratio_bps
  proof_assert result.collateral * 10000 - result.debt * result.min_ratio_bps ==
    engine.collateral * 10000 -
    engine.debt * engine.min_ratio_bps +
    amount * engine.min_ratio_bps
  proof_assert result.collateral + result.reserve - result.debt ==
    engine.collateral + engine.reserve - engine.debt + amount
  proof_assert repay_post(engine, amount, result)
  result
}

///|
/// Inject additional collateral. Each new collateral unit is worth `10000`
/// scaled headroom (because the collateral side of `headroom` is multiplied
/// by `10000`) and exactly `1` unit of equity. Like `repay`, there is no
/// extra ratio precondition: more collateral can never push the vault closer
/// to liquidation.
pub fn add_collateral(
  engine : Engine,
  amount : Int,
) -> Engine where {
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
  proof_assert (engine.collateral + amount) * 10000 ==
    engine.collateral * 10000 + amount * 10000
  proof_assert result.collateral * 10000 - result.debt * result.min_ratio_bps ==
    engine.collateral * 10000 -
    engine.debt * engine.min_ratio_bps +
    amount * 10000
  proof_assert result.collateral + result.reserve - result.debt ==
    engine.collateral + engine.reserve - engine.debt + amount
  proof_assert add_collateral_post(engine, amount, result)
  result
}

///|
/// The dual of `add_collateral`. The precondition is the integer form of
/// "the post-state is still above the minimum ratio", written directly on
/// `collateral - amount` so the solver can see it without re-deriving a
/// subtraction. Headroom drops by `amount * 10000`; equity drops by `amount`.
/// The withdrawal can shrink collateral all the way down to the exact ratio
/// boundary without triggering liquidation, because the precondition uses
/// `<=` rather than `<`.
pub fn withdraw_collateral(
  engine : Engine,
  amount : Int,
) -> Engine where {
  proof_require: healthy(engine),
  proof_require: 0 <= amount,
  proof_require: engine.debt * engine.min_ratio_bps <=
  (engine.collateral - amount) * 10000,
  proof_ensure: result => withdraw_post(engine, amount, result),
} {
  let result = {
    collateral: engine.collateral - amount,
    debt: engine.debt,
    reserve: engine.reserve,
    min_ratio_bps: engine.min_ratio_bps,
  }
  proof_assert (engine.collateral - amount) * 10000 ==
    engine.collateral * 10000 - amount * 10000
  proof_assert result.collateral * 10000 - result.debt * result.min_ratio_bps ==
    engine.collateral * 10000 -
    engine.debt * engine.min_ratio_bps -
    amount * 10000
  proof_assert result.collateral + result.reserve - result.debt ==
    engine.collateral + engine.reserve - engine.debt - amount
  proof_assert withdraw_post(engine, amount, result)
  result
}

///|
/// Top up the protocol reserve. Only requires `engine_inv` — *not* `healthy`
/// — because topping up the reserve is a rescue operation the protocol can
/// perform on an already-liquidatable vault. Headroom is unchanged, because
/// `headroom` looks only at collateral and debt; equity grows by `amount`,
/// which is the entire effect on the vault's books.
pub fn add_reserve(
  engine : Engine,
  amount : Int,
) -> Engine where {
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
  proof_assert result.collateral * 10000 - result.debt * result.min_ratio_bps ==
    engine.collateral * 10000 - engine.debt * engine.min_ratio_bps
  proof_assert result.collateral + result.reserve - result.debt ==
    engine.collateral + engine.reserve - engine.debt + amount
  proof_assert add_reserve_post(engine, amount, result)
  result
}

///|
/// The exact liquidation predicate, exposed as a runtime boolean. It is
/// `headroom(engine) < 0`, which is the strict negation of the healthy case
/// (`headroom >= 0`). The post-condition records the equivalence
/// `result == (healthy(engine) == false)` so callers that branch on this flag
/// can immediately discharge the `liquidatable` precondition of
/// `liquidate_all` in the `true` arm.
pub fn is_liquidatable(
  engine : Engine,
) -> Bool where {
  proof_require: engine_inv(engine),
  proof_ensure: result => liquidatable_post(engine, result),
} {
  let result = engine.collateral * 10000 - engine.debt * engine.min_ratio_bps <
    0
  proof_assert liquidatable_post(engine, result)
  result
}

///|
/// The full unwind sequence for an under-water vault. The intuition is a
/// simple two-step waterfall:
///
///   1. Seize all of the collateral. The vault's collateral field drops to
///      zero and the debt is reduced by the same amount (up to the full
///      debt). Any debt that the collateral could not cover is the
///      `deficit_after_collateral`.
///
///   2. Draw the deficit from the reserve. The reserve either absorbs the
///      whole deficit — in which case the next engine's debt is zero — or it
///      is drained to zero, and whatever debt still remains becomes the
///      `remaining_bad_debt` that the protocol has to socialize.
///
/// The loop-free computation in the body walks exactly this waterfall: the
/// `reserve_used` branch is the `min(deficit, reserve)` from
/// `reserve_used_to_close`, and the subtraction produces `uncovered_debt`.
/// The two trailing `proof_assert`s line the runtime values up with those
/// spec-level helpers so the post-condition falls out directly. The
/// post-condition in `stablecoin_engine.mbtp` encodes the disjunction
/// `reserve == 0 || debt == 0` on the next engine, which is the invariant
/// that characterizes a "fully settled" liquidation.
pub fn liquidate_all(
  engine : Engine,
) -> LiquidationResult where {
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
