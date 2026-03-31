---
name: moonbit-proof-refinement
description: Use when working on MoonBit verification for data structures, abstraction functions, refinement invariants, Why3-backed proof modeling, or reducing trusted proof bridges. Especially relevant for packages like avl, sparse_array, fmap, and fset.
---

# MoonBit Proof Refinement

Use this skill for MoonBit proof engineering on verified data structures.

## Core Pattern

Split the proof into two layers:

- `.mbtp`: proof model
  - abstraction functions like `abs(x)`
  - representation invariants like `ok(x)`
  - proof-only predicates describing postconditions
  - reusable lemmas
- `.mbt`: implementation
  - executable code
  - contracts over the `.mbtp` predicates
  - local `proof_assert` steps to guide VC solving

Follow the `avl` style:

- define proof facts in `.mbtp`
- use `proof_assert` in `.mbt`
- avoid adding callable “lemma wrapper” functions unless the frontend forces a temporary bridge

## Preferred Workflow

1. Define the abstract model first.
   - Prefer named predicates such as `empty_ok`, `insert_ok`, `lookup_ok`.
   - Keep contracts stated against those predicates instead of large inline formulas.

2. Define the implementation invariant second.
   - State only the facts needed for safe indexing and model connection.
   - Avoid overloading the invariant with every semantic property.

3. Put generic proof imports in shim packages.
   - `fmap`/`fset` proof imports belong in `fmap.mbtp` / `fset.mbtp`, not repeated in each client package.
   - Client `.mbtp` files should mostly contain domain-specific logic.

4. In implementation code, assert concrete facts immediately after construction.
   - After building a record or array, add `proof_assert` for the obvious facts the solver may miss.
   - Example shapes:
     - `proof_assert data.length() == 1`
     - `proof_assert data[0] == value`
     - `proof_assert raw_uint_to_int(bitmap, 0) == pow2_value(idx, 0)`

5. Use `proof_assert` instead of callable proof wrappers when possible.
   - This is the normal pattern for bridging from code to the proof model.
   - Only keep a trusted contracted helper in `.mbt` when direct assertion still times out.

6. Shrink the trusted surface from the outside in.
   - Constructors first: `empty`, `singleton`
   - Observers next: `length`, `get`
   - Mutators last: `add`, `replace`, `remove`

## Tactics That Help

- Name proof goals with predicates.
  - Good: `singleton_abs_ok(result, idx, value)`
  - Bad: repeating full `fmap_eq(abs(...), ...)` formulas in every contract

- Introduce tiny helper facts instead of giant theorems.
  - Prefer “zero bitmap has count 0” over “empty sparse array refines to empty fmap”.
  - Prefer “singleton data has length 1” as a local `proof_assert`.

- Separate proof-shape refactors from proof-strength changes.
  - First move the statement into `.mbtp`.
  - Then try to prove it.
  - If it still fails, decide whether to keep a temporary trusted bridge.

- Watch for solver perturbation.
  - New lemmas can make unrelated VCs slower or timeout.
  - After each added lemma, rerun the whole package proof, not just the target VC.

- Read the generated proof report before adding lemmas.
  - Target the exact failing VC.
  - Distinguish:
    - missing arithmetic/index fact
    - missing abstraction fact
    - bad quantifier instantiation
    - frontend limitation

## Sparse Structure Guidance

For structures like sparse arrays:

- model domain separately from payload
- keep `rank`/`count` logic in `.mbtp`
- connect dense storage to abstract keys through the abstraction function

Recommended split:

- concrete fields: bitmap + dense array
- `ok(x)`: only bounds/layout facts
- `abs(x)`: map/set interpretation
- postcondition predicates: extensional behavior of operations

For constructor proofs:

- assert concrete shape facts first
- then assert the named postcondition predicate
- if that still times out, add smaller helper lemmas below the abstraction, not another giant top-level theorem

## Trust Policy

Treat trusted helpers as temporary bridges, not design endpoints.

When a trusted helper remains:

- keep it narrow
- make its preconditions concrete
- target one named predicate in the postcondition
- leave the mathematical statement in `.mbtp`

Preferred order for deleting trust:

1. constructor bridges
2. observer bridges
3. update bridges
4. bitmap bridges

## Validation Loop

After every proof edit:

- `moon check <pkg>`
- `moon prove <pkg>`
- if runtime code changed: `moon test <pkg>`

When a proof regresses:

- inspect `_build/verif/<pkg>/<pkg>.proof.json`
- identify the exact VC and local context
- only then decide whether to add:
  - `proof_assert`
  - a helper predicate
  - a helper lemma
  - or a temporary trusted bridge

## Anti-Patterns

- Repeating raw `#proof_import` bindings in every client proof file
- Using large trusted wrapper functions when a local `proof_assert` would do
- Changing both abstraction design and solver guidance in one step
- Adding helper lemmas without rerunning the full package proof
- Treating timeouts as proof failures without checking if the lemma changed solver behavior elsewhere
