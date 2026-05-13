# Finance Examples

These packages are domain-specific verification examples for finance, custody,
auction, and risk-control workflows. Each package is executable MoonBit code
with proof obligations discharged through the Why3 backend.

## Packages

| Package | Domain | What it verifies |
|---------|--------|------------------|
| `stablecoin_engine` | Stablecoins / protocol solvency | Mint, repay, withdraw, and liquidate flows preserve collateralization and account for residual bad debt. |
| `margin_engine` | Perpetuals / exchange risk | Liquidation boundaries, funding debits, partial close behavior, and deleveraging restore maintenance margin. |
| `clearinghouse_waterfall` | Exchanges / risk mutualization | Default losses are allocated through insurance, junior capital, senior capital, and socialized loss. |
| `bridge_custody` | Bridges / custody | Withdrawals consume fresh nonces, preserve the remaining nonce set, and reduce reserves by the withdrawn amount. |
| `cpmm_swap` | DeFi / AMMs | Fee-adjusted swap quotes keep reserve updates bounded and preserve the pool invariant. |
| `ltv_lending` | Lending / credit | Borrow, repay, and collateral updates preserve solvency and risk-buffer accounting. |
| `batch_auction` | Exchanges / market structure | Binary search identifies the matched/unmatched frontier and keeps the clearing price inside the marginal spread. |
| `risk_limits` | Brokerage / risk | The monitor returns the earliest breached account or proves the full exposure envelope is safe. |
| `vesting_stream` | Tokenomics / treasury | Vesting, claimable amount, and release logic stay bounded by the total grant. |
| `threshold_multisig` | Governance / custody | Approval counting matches the vote array and execution is allowed exactly when the threshold is met. |

## Running

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
