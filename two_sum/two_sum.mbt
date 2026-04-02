///|
pub fn first_hit(
  a : FixedArray[Int],
  sum : Int,
) -> (Int, Int)? where {
  proof_ensure: result => two_sum_result_ok(a, sum, result),
} {
  for i = 0; i < a.length(); {
    let row_hit = for j = 0; j < a.length(); {
      if a[i] + a[j] == sum {
        break Some((i, j))
      } else {
        continue j + 1
      }
    } nobreak {
      None
    } where {
      proof_invariant: 0 <= j,
      proof_invariant: j <= a.length(),
      proof_invariant: no_two_sum_before_i(a, sum, i),
      proof_invariant: no_two_sum_before_j(a, sum, i, j),
      proof_yield: res => first_hit_row_ok(a, sum, i, res),
      reasoning: (
        #| This inner loop exhaustively searches row `i`: before each iteration,
        #| `no_two_sum_before_j(a, sum, i, j)` states that no partner in
        #| `[0, j)` works with `a[i]`.
        #|
        #| If `a[i] + a[j] == sum`, we can immediately yield `Some((i, j))`.
        #| Otherwise we advance `j`, extending the proven no-hit prefix by one.
        #|
        #| The outer invariant `no_two_sum_before_i(a, sum, i)` is untouched by
        #| the inner scan, since it concerns earlier rows only.
        #|
        #| The measure `a.length() - j` decreases each step.
        #|
        #| Exiting with `None` means the whole row has been checked, so the
        #| yielded summary is exactly `first_hit_row_ok(a, sum, i, None)`.
      ),
    }
    match row_hit {
      Some((ri, rj)) => break Some((ri, rj))
      None => continue i + 1
    }
  } nobreak {
    None
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= a.length(),
    proof_invariant: no_two_sum_before_i(a, sum, i),
    proof_yield: res => two_sum_result_ok(a, sum, res),
    reasoning: (
      #| The outer loop scans candidate first indices row by row. The invariant
      #| `no_two_sum_before_i(a, sum, i)` means every row `< i` has already been
      #| proved to contain no solution.
      #|
      #| A successful inner-loop result is already a valid witness, so the
      #| `proof_yield` clause discharges the early break case directly.
      #|
      #| If a row finishes with `None`, the inner summary upgrades the outer
      #| invariant from rows `< i` to rows `< i + 1`.
      #|
      #| The measure `a.length() - i` decreases as we advance through rows.
      #|
      #| Therefore, reaching the normal exit means every row has been ruled out,
      #| which is exactly the `None` branch of `two_sum_result_ok`.
    ),
  }
}

///|
pub fn one_loop_positive(
  a : FixedArray[Int],
  sum : Int,
) -> (Int, Int)? where {
  proof_require: nonnegative(sum),
  proof_require: nonnegative_entries(a),
  proof_ensure: result => positive_two_sum_result_ok(a, sum, result),
} {
  let seen = FixedArray::make(sum + 1, 0)
  for i = 0; i < a.length(); {
    if a[i] <= sum {
      let complement = sum - a[i]
      if complement == a[i] {
        break Some((i, i))
      } else {
        let j = seen[complement]
        if j != 0 {
          break Some((i, j - 1))
        } else {
          seen[a[i]] = i + 1
          continue i + 1
        }
      }
    } else {
      continue i + 1
    }
  } nobreak {
    None
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= a.length(),
    proof_invariant: seen.length() == sum + 1,
    proof_invariant: no_two_sum_in_prefix(a, sum, i),
    proof_invariant: seen_complete(seen, a, i),
    proof_invariant: seen_sound(seen, a, i),
    proof_yield: res => positive_two_sum_result_ok(a, sum, res),
    reasoning: (
      #| `seen` is a lookup table over values in `[0, sum]`, stored with a
      #| one-based encoding so that `0` can mean “not seen yet”.
      #|
      #| `seen_complete` says every value present in the processed prefix is
      #| marked in the table, while `seen_sound` says every nonzero table entry
      #| points back to an actual prefix index with that value.
      #|
      #| For the current `a[i]`:
      #|   - If `a[i] > sum`, no nonnegative partner can make the target sum, so
      #|     skipping it preserves the invariants.
      #|   - If `complement == a[i]`, the pair `(i, i)` is a direct witness.
      #|   - If `seen[complement] != 0`, soundness gives an earlier witness index.
      #|   - Otherwise we record `a[i]`, and completeness/soundness extend to the
      #|     larger prefix.
      #|
      #| The measure `a.length() - i` decreases each step.
      #|
      #| Reaching `None` means the whole prefix is the whole array, and
      #| `no_two_sum_in_prefix(a, sum, i)` becomes the required absence result.
    ),
  }
}
