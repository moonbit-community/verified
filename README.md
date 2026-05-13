# MoonBit Formal Verification with `moon prove`

This project demonstrates MoonBit's experimental `moon prove` command, which
enables formal verification of MoonBit programs by lowering specifications to
[Why3](https://why3.lri.fr/) and discharging proof obligations with SMT
solvers such as [Z3](https://github.com/Z3Prover/z3), CVC5, and Alt-Ergo.

## How it works

The pipeline has three stages:

```
 .mbt + .mbtp          moonc prove             Why3 + Z3
┌────────────┐      ┌──────────────┐      ┌──────────────┐
│ Source code │ ───► │ Generate     │ ───► │ Prove goals  │
│ + predicates│      │ WhyML (.mlw) │      │ via SMT      │
└────────────┘      └──────────────┘      └──────────────┘
```

### 1. User writes specifications

Each package contains two source files:

- **`.mbt`** — MoonBit code with contracts and loop invariants
- **`.mbtp`** — Predicate definitions used in contracts

**Predicates** (`.mbtp`) define logical properties using first-order logic:

```moonbit
predicate in_bounds(xs : FixedArray[Int], i : Int) {
  (0 <= i) && (i < xs.length())
}

predicate sorted(xs : FixedArray[Int]) {
  ∀ i : Int, ∀ j : Int,
    ((in_bounds(xs, i)) && (in_bounds(xs, j)) && (i <= j)) →
      xs[i] <= xs[j]
}
```

**Contracts** (`.mbt`) annotate functions with preconditions, postconditions,
and loop invariants:

```moonbit
pub fn lower_bound(xs : FixedArray[Int], key : Int) -> Int where {
  proof_require: sorted(xs),
  proof_ensure: result => lower_bound_ok(xs, key, result),
} {
  for lo = 0, hi = xs.length(); lo < hi; {
    let mid = lo + (hi - lo) / 2
    if xs[mid] < key {
      continue mid + 1, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  } where {
    proof_invariant: 0 <= lo,
    proof_invariant: lo <= hi,
    proof_invariant: hi <= xs.length(),
    proof_invariant: all_less_before(xs, key, lo),
    proof_invariant: all_geq_from(xs, key, hi),
  }
}
```

- `proof_require: pred(...)` — precondition (assumed true on entry)
- `proof_ensure: result => pred(..., result)` — postcondition (must hold on exit; `result`
  refers to the return value)
- `where { proof_invariant: expr, ... }` — loop invariants (must hold at every
  iteration boundary)

### 2. Lowering to WhyML

`moonc prove` compiles each package's `.mbt` + `.mbtp` into a WhyML module
(`.mlw`) under `_build/verif/<pkg>/`. The key transformations are:

| MoonBit | WhyML |
|---------|-------|
| `FixedArray[Int]` | `array int` |
| `xs.length()` | `xs.length` |
| `xs[i]` | `xs[i]` |
| `&&` / `\|\|` | `/\` / `\/` |
| `∀ x : Int,` | `forall x : int.` |
| `→` | `->` |
| `for` loop | `while` loop with `ref` variables |
| loop invariants | `invariant { ... }` clauses |
| `proof_require` / `proof_ensure` | `requires { ... }` / `ensures { ... }` |

The compiler also auto-generates a **termination variant** for each loop
(e.g. `variant { hi - lo }` for a loop with condition `lo < hi`), and links
all predicates from the `.mbtp` file with Why3's `with` keyword for mutual
recursion.

Integers are mathematical (unbounded) in Why3, so there are no overflow
concerns. The WhyML modules import `int.Int`, `int.ComputerDivision`,
`ref.Ref`, and `array.Array` from the Why3 standard library.

### 3. Proving with Why3 + Z3

Why3 breaks the WhyML specification into individual **proof obligations**
(goals). Each goal is a logical formula that Z3 must discharge. Typical goals:

- **Loop invariant initialization** — invariant holds before the first iteration
- **Loop invariant preservation** — if invariant holds before an iteration and
  the loop condition is true, it holds after the iteration body
- **Postcondition** — the ensures clause holds when the function returns
- **Termination** — the variant decreases and stays non-negative
- **Array bounds** — array accesses are within bounds

The proving strategy (`MoonBit_Auto` in `_build/verif/why3.conf`) runs
Alt-Ergo, Z3, and CVC5 in multiple passes with increasing timeouts:

```
Alt-Ergo/Z3/CVC5 @ 0.2s, 1000 MB   →  quick wins
Alt-Ergo/Z3/CVC5 @ 1s,   1000 MB   →  moderate goals
compute_specified                      →  unfold definitions
split_vc                               →  break conjunction goals apart
Alt-Ergo/Z3/CVC5 @ 2s,   4000 MB   →  harder goals
```

CI uses a checked-in `.github/why3.conf` with the same prover set and longer
timeouts to reduce solver-variance failures on shared runners.

Results are written to `_build/verif/<pkg>/<pkg>.proof.json` with per-goal
status (valid, timeout, unknown, etc.).

## Running

```sh
moon prove
```

This verifies all packages in the workspace. Output shows per-package results
and a summary of total goals proved.

## Package Map

The repository is a mixed collection of reusable proof infrastructure,
verified libraries, small proof demos, and larger finance case studies. The
curated packages are grouped by intent:

- `libs/*` contains low-level proof support packages used by other packages.
- Top-level data-structure packages are the main reusable verified libraries.
- `examples/demos/*` contains compact proof exercises and algorithm examples.
- `examples/finance/*` contains larger finance-specific case studies.

Other top-level scratch or probe directories are development artifacts, not
part of the curated package set.

### Core Proof Libraries

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
| `libs/bitmap32` | Trusted UInt/bitmap bridge helpers |
| `libs/bytes` | Byte-oriented proof support |

### Verified Data Structures

These packages are closer to reusable libraries: they expose data-structure
APIs with representation invariants and semantic model postconditions.

| Package | What it verifies |
|---------|------------------|
| `vector` | Persistent vector operations against a sequence model |
| `sparse_array` | Bitmap-backed sparse array against a finite-map model |
| `avl` | AVL tree balancing, insertion, deletion, and set model preservation |
| `leftist_heap` | Heap merge and minimum invariants |
| `skew_heap` | Heap merge and minimum invariants |
| `pairing_heap` | Pairing heap structure and heap-order properties |
| `stack_min` | Stack operations with tracked minimum |

### Algorithm Demos

These are compact verification examples. They are useful for learning proof
patterns, loop invariants, binary-search invariants, quantified assertions, and
small arithmetic facts.

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

### Finance Case Studies

These packages model finance, custody, auction, and risk-control workflows.
For a market-facing overview, see [INVESTOR_SHOWCASE.md](INVESTOR_SHOWCASE.md).

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

## Known limitations

See [TODO.md](TODO.md) for detailed writeups. Summary:

1. **Sequential `continue` assignment** — `continue i + 1, i` sets the second
   variable to the *updated* `i`. Use a `let` binding to capture the old value.

2. **Contracts work best with named predicates** — complex inline boolean
   expressions are brittle. Define a named predicate in `.mbtp` and reference
   it from `proof_require` / `proof_ensure`.

3. **`∀` must be at the top level of a predicate body** — cannot be nested
   inside `&&`. Move conditions into the implication consequent instead.

4. **Loop variant requires `loopvar < expr` condition** — conditions like
   `r >= b` or `lo + 1 < hi` produce no termination variant. Use
   `lo < hi - 1` (recognized as `loopvar < expr`) or restructure the algorithm.
