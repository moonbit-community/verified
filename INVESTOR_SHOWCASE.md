# Investor Showcase

This branch adds seven finance and crypto examples that are intentionally more
business-facing than the baseline algorithm demos. Each one is executable
MoonBit code with proof obligations discharged through the Why3 backend.

## Packages

| Package | Domain | What is proved | Why it matters |
|---------|--------|----------------|----------------|
| `stablecoin_engine` | Stablecoins / protocol solvency | Safe mint/repay/withdraw transitions preserve collateralization exactly, and full liquidation computes exact residual bad debt after consuming collateral and reserve. | This is the flagship example: it is much closer to a real protocol safety story than a standalone math primitive. |
| `cpmm_swap` | DeFi / AMMs | The fee-adjusted quote is a valid floor quote, output never drains reserves, and the post-swap pool invariant does not decrease. | Shows protocol math, slippage control, and reserve safety in one compact example. |
| `ltv_lending` | Lending / credit | `max_safe_debt` is the exact floor of the LTV bound, and `borrow`, `repay`, and `add_collateral` preserve solvency while updating the risk buffer exactly. | Demonstrates provable collateral safety and deterministic risk accounting. |
| `batch_auction` | Exchanges / market structure | A binary search finds the exact frontier between matched and unmatched orders, and the returned clearing price stays inside the marginal spread. | Shows that formal methods can certify a realistic market-clearing engine, not just toy arithmetic. |
| `risk_limits` | Brokerage / risk | The monitor either returns the earliest breached account or proves the entire portfolio envelope is safe. | Useful as a provable first-line control for limit and exposure monitoring. |
| `vesting_stream` | Tokenomics / treasury | Linear vesting is bounded by the total grant, `claimable` never goes negative, and `release` cannot over-distribute tokens. | Captures a very common token-distribution primitive with strong safety guarantees. |
| `threshold_multisig` | Governance / custody | The approval counter exactly matches the number of `1` votes, and execution is allowed iff the threshold is met. | Gives a simple but credible on-chain/off-chain governance proof example. |

## How To Demo

Run everything:

```sh
moon prove
moon test
```

Or demo just the showcase packages one by one:

```sh
moon prove stablecoin_engine
moon prove cpmm_swap
moon prove ltv_lending
moon prove batch_auction
moon prove risk_limits
moon prove vesting_stream
moon prove threshold_multisig
```

## Caveats

If you only show one package in a pitch, show `stablecoin_engine` first. It is
the closest thing in the repo to a protocol-level solvency guarantee.

The current proof/backend limitations I found while building these examples are
tracked in [PROOF_SYSTEM_FINDINGS.md](PROOF_SYSTEM_FINDINGS.md). The most
important practical caveat is that proofs use mathematical integers, while
runtime execution can still overflow if arithmetic-heavy examples are fed large
unchecked values.
