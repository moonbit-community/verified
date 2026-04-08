# MoonBit Formal Verification with `moon prove`

This project demonstrates MoonBit's experimental `moon prove` command, which
enables formal verification of MoonBit programs by lowering specifications to
[Why3](https://why3.lri.fr/) and discharging proof obligations with the
[Z3](https://github.com/Z3Prover/z3) SMT solver.

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

The proving strategy (`MoonBit_Auto` in `_build/verif/why3.conf`) runs Z3 in
multiple passes with increasing timeouts:

```
Z3 @ 0.2s, 1000 MB   →  quick wins
Z3 @ 1s,   1000 MB   →  moderate goals
compute_specified      →  unfold definitions
split_vc               →  break conjunction goals apart
Z3 @ 2s,   4000 MB   →  harder goals
```

Results are written to `_build/verif/<pkg>/<pkg>.proof.json` with per-goal
status (valid, timeout, unknown, etc.).

## Running

```sh
moon prove
```

This verifies all packages in the workspace. Output shows per-package results
and a summary of total goals proved.

## Examples

The project contains a compact set of example packages at increasing difficulty:

### No loops (branch-only proofs)

| Package | What it proves |
|---------|---------------|
| `abs` | `\|x\| >= 0` and equals `x` or `-x` |
| `maxfn` | `max(a,b) >= a`, `>= b`, and equals one of them |
| `clamp` | `lo <= clamp(x, lo, hi) <= hi` given `lo <= hi` |

### Simple loops

| Package | What it proves |
|---------|---------------|
| `find` | Linear search: result is -1 or a valid index with matching key |
| `count` | Count non-negatives: `0 <= result <= length` |
| `gauss` | Sum 1..n: `result * 2 == n * (n + 1)` (Gauss formula) |

### Binary search variants

| Package | What it proves |
|---------|---------------|
| `binary_search` | Option-returning binary search with strong window invariants |
| `invpred` | Binary search using a named invariant predicate |
| `isqrt` | Integer square root via binary search: `r*r <= n < (r+1)*(r+1)` |
| `div` | Integer division via binary search: `q*b <= a < (q+1)*b` |

### Quantified invariants

| Package | What it proves |
|---------|---------------|
| `maxarr` | Index of max element: `∀ k, xs[k] <= xs[result]` |
| `lowerbound` | Lower bound binary search: `∀ i < result, xs[i] < key` and `∀ i >= result, xs[i] >= key` — combines quantified invariants with sorted precondition |
| `sumbounds` | Array sum bounded by element range: `lo*n <= sum <= hi*n` — nonlinear arithmetic with quantified precondition |
| `checksorted` | If result == 1, all adjacent pairs in order — connects a boolean flag to a quantified property |
| `arreq` | Two-array equality: if result == 1, `∀ k, xs[k] == ys[k]` |

## Investor-Grade Crypto / Finance Showcase

For more market-facing examples, see [INVESTOR_SHOWCASE.md](INVESTOR_SHOWCASE.md).
The new packages are:

- `stablecoin_engine` — verified mint/repay/withdraw/liquidate flows with exact bad-debt resolution
- `cpmm_swap` — fee-adjusted constant-product AMM swap math with reserve-safety and invariant proofs
- `ltv_lending` — solvency-preserving lending operations with exact risk-buffer accounting
- `batch_auction` — verified uniform-price batch-auction frontier search
- `risk_limits` — earliest-breach risk monitor for bounded exposure envelopes
- `vesting_stream` — bounded token vesting and release logic
- `threshold_multisig` — exact threshold execution via counted approvals

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
