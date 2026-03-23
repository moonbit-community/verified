///|
#ensures(two_sum_result_ok(a, sum, result))
pub fn first_hit(a : FixedArray[Int], sum : Int) -> (Int, Int)? {
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
  }
}

///|
#requires(nonnegative(sum))
#requires(nonnegative_entries(a))
#ensures(positive_two_sum_result_ok(a, sum, result))
pub fn one_loop_positive(a : FixedArray[Int], sum : Int) -> (Int, Int)? {
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
  }
}
