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

### `#requires` / `#ensures` only accept predicate calls

Inline boolean expressions like `#requires(lo <= hi)` cause a syntax error.
A named predicate must be defined in the `.mbtp` file and referenced by name.

```moonbit
// ✗ Does not work
#requires(lo <= hi)

// ✓ Works — define predicate in .mbtp
predicate valid_bounds(lo : Int, hi : Int) { lo <= hi }
// then in .mbt
#requires(valid_bounds(lo, hi))
```
