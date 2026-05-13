# Investor Showcase

This branch adds ten finance and crypto examples that are intentionally more
business-facing than the baseline algorithm demos. Each one is executable
MoonBit code with proof obligations discharged through the Why3 backend.

## Packages

| Package | Domain | What is proved | Why it matters |
|---------|--------|----------------|----------------|
| `examples/finance/stablecoin_engine` | Stablecoins / protocol solvency | Safe mint/repay/withdraw transitions preserve collateralization exactly, and full liquidation computes exact residual bad debt after consuming collateral and reserve. | This is the flagship example: it is much closer to a real protocol safety story than a standalone math primitive. |
| `examples/finance/margin_engine` | Perpetuals / exchange risk | Liquidation price is an exact integer boundary, funding debits consume margin buffer exactly, partial close preserves mark-to-market equity, and auto-deleveraging closes the minimum position needed to restore maintenance margin. | This is the strongest trading-engine example in the repo because it proves a realistic deleveraging control rather than just static collateral math. |
| `examples/finance/clearinghouse_waterfall` | Exchanges / risk mutualization | A default is resolved through insurance, junior capital, senior capital, and finally socialized loss, with the exact loss split proved. | This is a stronger institutional-risk story than simple collateral math because it certifies the whole loss waterfall. |
| `examples/finance/bridge_custody` | Bridges / custody | Every withdrawal consumes a fresh nonce exactly once, preserves the rest of the nonce set, and reduces reserves by the exact amount. | Shows replay protection and custody safety with an explicit state model, not just scalar accounting. |
| `examples/finance/cpmm_swap` | DeFi / AMMs | The fee-adjusted quote is a valid floor quote, output never drains reserves, and the post-swap pool invariant does not decrease. | Shows protocol math, slippage control, and reserve safety in one compact example. |
| `examples/finance/ltv_lending` | Lending / credit | `max_safe_debt` is the exact floor of the LTV bound, and `borrow`, `repay`, and `add_collateral` preserve solvency while updating the risk buffer exactly. | Demonstrates provable collateral safety and deterministic risk accounting. |
| `examples/finance/batch_auction` | Exchanges / market structure | A binary search finds the exact frontier between matched and unmatched orders, and the returned clearing price stays inside the marginal spread. | Shows that formal methods can certify a realistic market-clearing engine, not just toy arithmetic. |
| `examples/finance/risk_limits` | Brokerage / risk | The monitor either returns the earliest breached account or proves the entire portfolio envelope is safe. | Useful as a provable first-line control for limit and exposure monitoring. |
| `examples/finance/vesting_stream` | Tokenomics / treasury | Linear vesting is bounded by the total grant, `claimable` never goes negative, and `release` cannot over-distribute tokens. | Captures a very common token-distribution primitive with strong safety guarantees. |
| `examples/finance/threshold_multisig` | Governance / custody | The approval counter exactly matches the number of `1` votes, and execution is allowed iff the threshold is met. | Gives a simple but credible on-chain/off-chain governance proof example. |

## How To Demo

Run everything:

```sh
moon prove
moon test
```

Or demo just the showcase packages one by one:

```sh
moon prove examples/finance/stablecoin_engine
moon prove examples/finance/margin_engine
moon prove examples/finance/clearinghouse_waterfall
moon prove examples/finance/bridge_custody
moon prove examples/finance/cpmm_swap
moon prove examples/finance/ltv_lending
moon prove examples/finance/batch_auction
moon prove examples/finance/risk_limits
moon prove examples/finance/vesting_stream
moon prove examples/finance/threshold_multisig
```

## Caveats

If you only show one package in a pitch, show
`examples/finance/stablecoin_engine` first. If you show two, pair it with
`examples/finance/margin_engine` for a stronger trading-risk story, or with
`examples/finance/clearinghouse_waterfall` for a fuller
prevention-plus-loss-containment story.

The current proof/backend limitations I found while building these examples are
tracked in [PROOF_SYSTEM_FINDINGS.md](PROOF_SYSTEM_FINDINGS.md). The most
important practical caveat is that proofs use mathematical integers, while
runtime execution can still overflow if arithmetic-heavy examples are fed large
unchecked values.
