# TODO / Known Issues

## Discovered Issues

### Sequential assignment in `continue` with multiple loop variables

When a `for` loop uses `continue expr1, expr2` where `expr2` references a variable
updated by `expr1`, the lowering to WhyML generates sequential assignments.
This means the second variable sees the **updated** value, not the original.

**Example:**

```moonbit
for i = 0, found = -1; i < xs.length(); {
  if xs[i] == key {
    continue i + 1, i   // found gets i+1, not i!
  } else {
    continue i + 1, found
  }
}
```

The WhyML lowers `continue i + 1, i` to:

```whyml
i <- (i + 1); found <- i   (* found = i+1, not the original i *)
```

**Workaround:** Use a `let` binding to capture the value before `continue`:

```moonbit
let new_found = if xs[i] == key { i } else { found }
continue i + 1, new_found
```

### `proof_require` / `proof_ensure` work best with named predicates

Inline boolean expressions directly inside contracts are less robust than a
named predicate in the `.mbtp` file.

```moonbit
// Less robust
pub fn clamp(x : Int, lo : Int, hi : Int) -> Int where {
  proof_require: lo <= hi,
} { ... }

// Recommended — define predicate in .mbtp
predicate valid_bounds(lo : Int, hi : Int) { lo <= hi }
// then in .mbt
pub fn clamp(x : Int, lo : Int, hi : Int) -> Int where {
  proof_require: valid_bounds(lo, hi),
} { ... }
```

### `∀` (forall) must be at the top level of a predicate body

The universal quantifier `∀` cannot be nested inside `&&`. It must appear
at the outermost level of the predicate body.

```moonbit
// ✗ Does not parse — ∀ nested inside &&
predicate is_max(xs : FixedArray[Int], idx : Int) {
  (0 <= idx) && (idx < xs.length()) &&
  (∀ k : Int, ((0 <= k) && (k < xs.length())) → xs[k] <= xs[idx])
}

// ✓ Works — ∀ at top level, extra conditions in the consequent
predicate is_max(xs : FixedArray[Int], idx : Int) {
  ∀ k : Int, ((0 <= k) && (k < xs.length())) →
    ((xs[k] <= xs[idx]) && (0 <= idx) && (idx < xs.length()))
}
```

### Loop variant auto-generation requires `loopvar < expr` condition pattern

The termination variant is only auto-generated when the loop condition matches
the pattern `loopvar < expr` (e.g. `i < j`, `i < xs.length()`). Other patterns
like `(r + 1) * (r + 1) <= n` or `r >= b` produce **no variant**, causing a
termination proof failure.

```moonbit
// ✗ No variant generated — condition is not `loopvar < expr`
for r = 0; (r + 1) * (r + 1) <= n; { continue r + 1 }
for r = a; r >= b; { continue r - b }

// ✗ Also fails — `lo + 1 < hi` has an expression on the left
for lo = 0, hi = n + 1; lo + 1 < hi; { ... }

// ✓ Works — `lo < hi - 1` is recognized as `loopvar < expr`
for lo = 0, hi = n + 1; lo < hi - 1; { ... }
```

**Workaround:** Restructure algorithms to use binary search patterns with
`lo < hi - 1` or `lo < hi` conditions. For example, integer square root and
division by subtraction can both be reformulated as binary search.
