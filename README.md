# MoonBit Verified Examples

This repository collects MoonBit packages that use the experimental
`moon prove` command to verify contracts, loop invariants, and data-structure
properties through Why3-backed SMT solving.

The project is organized into reusable proof support, verified data structures,
compact proof demos, and finance-oriented case studies.

## Running

Verify every package:

```sh
moon prove
```

Run executable tests:

```sh
moon test
```

CI uses a checked-in `.github/why3.conf` with Alt-Ergo, Z3, and CVC5. Local
`moon prove` also generates proof reports under `_build/verif/`.

## Package Layout

- `libs/*` contains low-level proof support packages used by other packages.
- Top-level data-structure packages are the main reusable verified libraries.
- `examples/demos/*` contains compact proof exercises and algorithm examples.
- `examples/finance/*` contains larger finance-specific case studies.

## Core Proof Libraries

These packages provide reusable logical models, proof shims, or low-level
bridges used by other packages.

| Package | Role |
|---------|------|
| `libs/mathint` | Mathematical integer helpers |
| `libs/seq` | Sequence model imports and operations |
| `libs/fset` | Finite-set model imports and operations |
| `libs/fmap` | Finite-map model imports and operations |
| `libs/readonlyarray` | Read-only array model bridge |
| `libs/bv32` | 32-bit bitvector model bridge |
| `libs/bitmap32` | UInt/bitmap bridge helpers |
| `libs/bytes` | Byte-oriented proof support |

## Verified Data Structures

These packages expose data-structure APIs with representation invariants and
semantic model postconditions.

| Package | What it verifies |
|---------|------------------|
| `vector` | Persistent vector operations against a sequence model |
| `sparse_array` | Bitmap-backed sparse array against a finite-map model |
| `avl` | AVL tree balancing, insertion, deletion, and set model preservation |
| `leftist_heap` | Heap merge and minimum invariants |
| `skew_heap` | Heap merge and minimum invariants |
| `pairing_heap` | Pairing heap structure and heap-order properties |
| `stack_min` | Stack operations with tracked minimum |

## Algorithm Demos

These packages are compact verification examples for proof patterns, loop
invariants, binary-search invariants, quantified assertions, and arithmetic
facts.

| Package | What it demonstrates |
|---------|----------------------|
| `examples/demos/abs` | Branch-only arithmetic postconditions |
| `examples/demos/clamp` | Range-bounded branch logic |
| `examples/demos/maxfn` | Maximum of two integers |
| `examples/demos/maxarr` | Maximum-element index with quantified array bounds |
| `examples/demos/find` | Linear search |
| `examples/demos/count` | Counting elements satisfying a predicate |
| `examples/demos/gauss` | Closed-form sum of `1..n` |
| `examples/demos/two_sum` | Pair search over arrays |
| `examples/demos/binary_search` | Option-returning binary search |
| `examples/demos/lowerbound` | Lower-bound binary search with quantified invariants |
| `examples/demos/invpred` | Binary search using a named invariant predicate |
| `examples/demos/isqrt` | Integer square root via binary search |
| `examples/demos/div` | Integer division via binary search |
| `examples/demos/bubble_sort` | Sorting loop invariants |
| `examples/demos/selection_sort` | Sorting loop invariants |
| `examples/demos/checksorted` | Relating a boolean flag to a quantified sortedness property |
| `examples/demos/arreq` | Two-array equality |
| `examples/demos/sumbounds` | Array sum bounded by element range |
| `examples/demos/cauchy_schwarz` | Arithmetic inequality proof |
| `examples/demos/bmh_bytes` | Byte-string search proof patterns |

## Finance Case Studies

These packages model finance, custody, auction, and risk-control workflows. For
more detail, see [examples/finance/README.md](examples/finance/README.md).

| Package | What it verifies |
|---------|------------------|
| `examples/finance/stablecoin_engine` | Mint/repay/withdraw/liquidate flows with bad-debt handling |
| `examples/finance/margin_engine` | Liquidation boundary, funding impact, and deleveraging logic |
| `examples/finance/clearinghouse_waterfall` | Multi-layer default waterfall accounting |
| `examples/finance/bridge_custody` | Replay-safe bridge withdrawals |
| `examples/finance/cpmm_swap` | Fee-adjusted constant-product AMM swap math |
| `examples/finance/ltv_lending` | Solvency-preserving lending operations |
| `examples/finance/batch_auction` | Uniform-price batch-auction frontier search |
| `examples/finance/risk_limits` | Earliest-breach risk monitor |
| `examples/finance/vesting_stream` | Bounded token vesting and release logic |
| `examples/finance/threshold_multisig` | Threshold execution via counted approvals |
