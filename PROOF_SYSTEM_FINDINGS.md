# Proof System Findings

This note records limitations I hit while constructing stronger crypto/finance
proof examples on top of MoonBit's current Why3-backed proof pipeline.

Date: 2026-04-08

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

## Suggested Future Improvements

The biggest unlock for finance-grade examples would be one of:

1. verified recursive logic functions over arrays with a supported termination
   annotation story
2. proof contracts on `#proof_pure` helpers
3. first-class logical summation/fold operators over array intervals

Any one of those would make exact conservation laws, PnL identities, and
weighted-voting/account-balance proofs much easier to encode cleanly.
