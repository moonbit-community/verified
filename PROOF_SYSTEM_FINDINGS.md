# Proof System Findings

This note records limitations I hit while constructing stronger crypto/finance
proof examples on top of MoonBit's current Why3-backed proof pipeline.

Date: 2026-04-09

## Confirmed Limits

### 1. `#proof_pure` functions cannot carry verification contracts

Direct experiment:

- I tried to define a recursive `#proof_pure` helper `prefix_sum(xs, upto)` in
  `.mbt` with a `where { proof_require: ..., proof_decrease: ... }` block.
- `moon prove scratch_sum` failed with:
  `pure functions cannot carry verification contracts yet`

Impact:

- This blocks the most direct way to write reusable ghost functions with
  explicit preconditions and termination measures.
- Exact finance-style conservation specs such as "`sum(delta) == 0`" are harder
  to express than scalar bounds or named logical predicates.

### 2. Recursive logic helpers in `.mbtp` need termination support that is not
obvious today

Direct experiment:

- I moved `prefix_sum(xs, upto)` into `.mbtp` as a logic function and removed
  the contracts.
- The parser accepted the file, but `moon prove scratch_sum` failed with:
  `Cannot prove termination for prefix_sum`

Impact:

- Recursive summaries over arrays are not plug-and-play today.
- This makes it expensive to encode exact prefix sums, weighted totals, and
  other ledger/accounting models directly in the proof layer.

### 3. `where` contracts on `.mbtp` logic functions did not work in this
experiment

Direct experiment:

- I tried attaching a `where { ... }` block to an `.mbtp` function definition.
- The compiler rejected it with an `unexpected where` parse error.

Interpretation:

- I do not yet know whether this is a general frontend limitation or a narrower
  syntax restriction in this release.
- For now, I am treating `.mbtp` functions as lightweight logical definitions
  and keeping proof obligations in predicates, lemmas, and executable code.

### 4. The proof model uses mathematical integers, while runtime execution can
still overflow

Direct experiment:

- In the `cpmm_swap` example, a deeper-liquidity runtime test using reserves of
  `5000 / 5000` produced the wrong output because the intermediate product
  `amount_in * fee_multiplier * reserve_out` overflowed at runtime.
- The proof still succeeded because the Why3 model reasons over unbounded
  mathematical integers.

Impact:

- Arithmetic-heavy finance/crypto examples can be proved correctly in the math
  model but still misbehave at runtime if inputs are not range-bounded.
- Demo code either needs explicit overflow preconditions or test inputs chosen
  to stay inside MoonBit runtime integer limits.

### 5. Some proof dependencies still need explicit direct package imports

Direct experiment:

- In the `bridge_custody` package, importing `bitmap32` was not enough for the
  proof pipeline even though `bitmap32` already depends on `bv32`.
- `moon prove bridge_custody` hit a compiler ICE until I added an explicit
  direct `bv32` dependency in `bridge_custody/moon.pkg`.

Impact:

- Proof dependency resolution is not fully robust across transitive proof-only
  requirements.
- When a package reuses proof-side definitions from another verified package,
  it may still need to import lower-level proof dependencies directly to keep
  the prover pipeline stable.

### 6. Mixed `&&` / `||` predicate tails can lower into a harder or misleading
proof shape

Direct experiment:

- In the `margin_engine` package, the original `min_close_to_restore_post`
  predicate ended with a conjunction followed by a parenthesized disjunction:
  `... && (result == 0 || frontier < 0)`.
- The generated WhyML for that predicate did not preserve the grouping in a
  solver-friendly way, and downstream callers could no longer easily recover
  earlier conjuncts such as `0 <= result`.
- Replacing the tail disjunction with a separate helper predicate
  `min_close_frontier(...)` fixed the issue immediately.

Impact:

- Complex finance predicates that mix conjunction and disjunction near the end
  of a formula are brittle today.
- In practice, it is safer to factor such case splits into a named helper
  predicate instead of relying on nested boolean structure inside one large
  postcondition.

## Practical Design Consequences

The current examples in this branch therefore bias toward proof shapes that the
toolchain handles well today:

- scalar algebraic invariants
- named postconditions in `.mbtp`
- quantified array predicates
- loop invariants over counters, bounds, and monotone search windows
- exact structural/refinement proofs for recursive data structures

I am intentionally avoiding proof designs that depend on:

- recursive ghost summaries over arrays with custom termination arguments
- pure helper functions that need preconditions
- large inline contract formulas instead of named predicates
- arithmetic demos with large unchecked intermediate products
- relying on transitive proof dependencies to be discovered automatically
- long mixed `&&` / `||` postconditions instead of smaller named helper
  predicates

## Suggested Future Improvements

The biggest unlock for finance-grade examples would be one of:

1. verified recursive logic functions over arrays with a supported termination
   annotation story
2. proof contracts on `#proof_pure` helpers
3. first-class logical summation/fold operators over array intervals

Any one of those would make exact conservation laws, PnL identities, and
weighted-voting/account-balance proofs much easier to encode cleanly.
