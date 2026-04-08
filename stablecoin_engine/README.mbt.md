# Stablecoin Engine

A verified integer-arithmetic model of a single-asset stablecoin vault. The
module exposes the minimum surface a collateralized stablecoin needs —
opening a position, minting and repaying debt, adjusting collateral, topping
up the reserve, and unwinding under-water vaults through liquidation — and
every public operation carries proof obligations that pin down exactly how
each action moves the books.

## What the Engine Tracks

An `Engine` is a four-field record:

| field | meaning |
|---|---|
| `collateral` | backing the user has posted |
| `debt` | stablecoin supply the user owes |
| `reserve` | protocol-owned buffer that absorbs losses on liquidation |
| `min_ratio_bps` | minimum collateralization ratio in basis points |

All ratios are kept as **basis points**: `10000` means 100%, `15000` means
150%, `20000` means 200%. The module pins `min_ratio_bps` to the window
`[10000, 30000]` so every ratio is both meaningful (at least 100%) and
bounded (at most 300%).

## Integer Arithmetic, Exact Boundary

There is no floating point anywhere in the module. Every ratio comparison is
rewritten into the cross-multiplied form

```
collateral * 10000  ≥  debt * min_ratio_bps
```

which is exact over `Int`. The signed quantity

```
headroom(engine) = collateral * 10000 - debt * min_ratio_bps
```

is the scaled distance from the liquidation edge: positive is healthy, zero
is the exact boundary, negative is liquidatable. This is the value the
public `safety_buffer` view returns, and it is what every mutation's
post-condition is written in terms of.

## The Invariant Ladder

Three predicates layer on top of each other, each adding a constraint to
the one below:

1. **`engine_inv`** — base shape: all three balances non-negative, ratio
   valid. Every constructor (`make_engine`, `open_engine`) establishes this
   and every mutation preserves it.
2. **`healthy`** — `engine_inv` plus `headroom(engine) >= 0`. This is the
   precondition of every user-facing mutation (`mint`, `repay`,
   `add_collateral`, `withdraw_collateral`) because those actions only make
   sense on a vault that is currently above the minimum ratio.
3. **`liquidatable`** — `engine_inv` plus `headroom(engine) < 0`. This is
   the precondition of `liquidate_all`, and it is exactly the negation of
   `healthy`, so any caller that branches on `is_liquidatable` can
   immediately discharge it in the `true` arm.

## Usage

### Opening a Fresh Position

Use `open_engine` for new, healthy vaults. It requires the initial debt to
already sit at or above the minimum ratio:

```mbt check
///|
test "opening a position at exactly 150% collateralization" {
  // 150 collateral, 100 debt, 20 reserve, 150% minimum ratio.
  // 100 * 15000 = 1_500_000, 150 * 10000 = 1_500_000, so headroom = 0.
  let engine = @stablecoin_engine.open_engine(150, 100, 20, 15000)
  assert_eq(@stablecoin_engine.safety_buffer(engine), 0)
  assert_eq(@stablecoin_engine.equity_value(engine), 70)
}
```

For test setups that deliberately start from an already-liquidatable state,
use `make_engine`, which only enforces the base shape invariant and does not
require the vault to be healthy.

### Sizing a Mint

`max_mintable(collateral, min_ratio_bps)` returns the exact integer floor
of the largest debt that `collateral` can back at that ratio. Its
post-condition encodes both sides of the floor — the returned value is a
valid debt, and one more would not be — so callers can size new mints
without redoing the arithmetic themselves.

```mbt check
///|
test "max mintable is the exact floor" {
  // At 150% minimum, 150 units of collateral back exactly 100 units of debt.
  assert_eq(@stablecoin_engine.max_mintable(150, 15000), 100)
  // 151 units of collateral still back only 100 units — the floor is tight.
  assert_eq(@stablecoin_engine.max_mintable(151, 15000), 100)
}
```

### Minting and Repaying

`mint` grows debt; `repay` shrinks it. The mint precondition enforces that
the post-state stays healthy, so the caller is responsible for bounding the
new debt against the current collateral. Repaying has no ratio precondition
because paying down debt can only improve headroom.

```mbt check
///|
test "mint to the boundary, then repay to rebuild headroom" {
  let engine = @stablecoin_engine.open_engine(150, 60, 20, 15000)
  // Minting 40 more brings debt to 100 and headroom to exactly 0.
  let minted = @stablecoin_engine.mint(engine, 40)
  assert_eq(minted.debt, 100)
  assert_eq(@stablecoin_engine.safety_buffer(minted), 0)
  // Repaying 20 pushes headroom back up by 20 * 15000 = 300_000.
  let repaid = @stablecoin_engine.repay(minted, 20)
  assert_eq(repaid.debt, 80)
  assert_eq(@stablecoin_engine.safety_buffer(repaid), 300_000)
}
```

### Adjusting Collateral

`add_collateral` grows the backing (each new unit is worth `10000` scaled
headroom); `withdraw_collateral` shrinks it but requires the post-state to
still sit above the minimum ratio. Either can shrink or grow headroom in
exact, predictable increments.

```mbt check
///|
test "withdraw collateral down to the ratio boundary" {
  let engine = @stablecoin_engine.open_engine(180, 80, 15, 15000)
  // Debt is 80, so the minimum collateral at 150% is 80 * 15000 / 10000 = 120.
  // Withdrawing 60 leaves collateral at exactly 120 — still valid.
  let after = @stablecoin_engine.withdraw_collateral(engine, 60)
  assert_eq(after.collateral, 120)
  assert_eq(@stablecoin_engine.safety_buffer(after), 0)
}
```

### Liquidation

When a vault's headroom goes negative, `is_liquidatable` returns `true` and
`liquidate_all` performs the two-step waterfall unwind:

1. Seize all collateral and apply it to the debt.
2. If debt still remains, draw on the reserve until either the deficit is
   covered or the reserve is drained.

The `LiquidationResult` records both steps: `reserve_used` and
`remaining_bad_debt`, plus the `next_engine` state (collateral zeroed,
reserve decreased). The post-condition guarantees
`next_engine.reserve == 0 || next_engine.debt == 0` — either the reserve
absorbed the loss completely, or it was drained and the leftover is carried
as bad debt.

```mbt check
///|
test "reserve fully absorbs a small shortfall" {
  // 120 collateral vs 100 debt, so no debt-side shortfall after seizing
  // collateral. The reserve is untouched.
  let engine = @stablecoin_engine.make_engine(120, 100, 10, 15000)
  assert_eq(@stablecoin_engine.is_liquidatable(engine), true)
  let result = @stablecoin_engine.liquidate_all(engine)
  assert_eq(result.reserve_used, 0)
  assert_eq(result.remaining_bad_debt, 0)
  assert_eq(result.next_engine.reserve, 10)
}
```

```mbt check
///|
test "reserve drains and leaves residual bad debt" {
  // 60 collateral vs 100 debt is a 40-unit shortfall. The reserve is only
  // 25, so it is drained to zero and 15 units of bad debt remain.
  let engine = @stablecoin_engine.make_engine(60, 100, 25, 15000)
  assert_eq(@stablecoin_engine.is_liquidatable(engine), true)
  let result = @stablecoin_engine.liquidate_all(engine)
  assert_eq(result.reserve_used, 25)
  assert_eq(result.remaining_bad_debt, 15)
  assert_eq(result.next_engine.reserve, 0)
  assert_eq(result.next_engine.debt, 15)
}
```

### Topping Up the Reserve

`add_reserve` is the only mutation that takes `engine_inv` rather than
`healthy` as a precondition, because a protocol rescue operation must be
able to inject reserve into an already-liquidatable vault. It leaves
`headroom` unchanged — the reserve does not appear in the ratio formula —
but it grows `equity_value` by the full amount.

```mbt check
///|
test "add_reserve works even when the vault is liquidatable" {
  let engine = @stablecoin_engine.make_engine(60, 100, 0, 15000)
  assert_eq(@stablecoin_engine.is_liquidatable(engine), true)
  let topped_up = @stablecoin_engine.add_reserve(engine, 50)
  // Headroom is unchanged — the reserve does not back the ratio.
  assert_eq(
    @stablecoin_engine.safety_buffer(topped_up),
    @stablecoin_engine.safety_buffer(engine),
  )
  assert_eq(topped_up.reserve, 50)
}
```

## What the Proof Guarantees

Every mutation's post-condition pins down the exact linear identity the
runtime body computes. For `mint(engine, amount)`, for example, the proof
records:

```
headroom(result) == headroom(engine) - amount * engine.min_ratio_bps
equity(result)   == equity(engine)   - amount
```

Combined with the invariant ladder, this means a caller that sequences a
series of mutations can derive the final `headroom` and `equity` values
from the inputs alone, with no rounding or off-by-one surprise at the
liquidation boundary. The integer arithmetic is exact everywhere, including
in the two-inequality floor characterization of `max_mintable` and in the
`reserve == 0 || debt == 0` disjunction that closes out every
`liquidate_all` result.
