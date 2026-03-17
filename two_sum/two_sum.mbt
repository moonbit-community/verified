///|
#ensures(two_loop_exists_ok(a, sum, result))
pub fn two_loop_exists(a : FixedArray[Int], sum : Int) -> Bool {
  for i = 0, found = false; i < a.length(); {
    let found_in_row = for j = 0, found = found; j < a.length(); {
      let next_found = found || a[i] + a[j] == sum
      continue j + 1, next_found
    } nobreak {
      found
    } where {
      invariant: 0 <= j,
      invariant: j <= a.length(),
      invariant: found ==
      (has_two_sum_before_i(a, sum, i) || has_two_sum_before_j(a, sum, i, j)),
    }
    continue i + 1, found_in_row
  } nobreak {
    found
  } where {
    invariant: 0 <= i,
    invariant: i <= a.length(),
    invariant: found == has_two_sum_before_i(a, sum, i),
  }
}

///|
#ensures(two_sum_result_ok(a, sum, result))
pub fn first_hit(a : FixedArray[Int], sum : Int) -> (Int, Int)? {
  let (found, ri, rj) = for i = 0, found = false, ri = 0, rj = 0; i < a.length(); {
    let (row_found, row_ri, row_rj) = for j = 0, found = found, ri = ri, rj = rj; j <
                                         a.length(); {
      if found {
        continue j + 1, true, ri, rj
      } else {
        let hit = a[i] + a[j] == sum
        let next_ri = if hit { i } else { ri }
        let next_rj = if hit { j } else { rj }
        continue j + 1, hit, next_ri, next_rj
      }
    } nobreak {
      (found, ri, rj)
    } where {
      invariant: 0 <= j,
      invariant: j <= a.length(),
      invariant: witness_state_ok(a, sum, found, ri, rj),
      invariant: found ==
      (has_two_sum_before_i(a, sum, i) || has_two_sum_before_j(a, sum, i, j)),
    }
    continue i + 1, row_found, row_ri, row_rj
  } nobreak {
    (found, ri, rj)
  } where {
    invariant: 0 <= i,
    invariant: i <= a.length(),
    invariant: witness_state_ok(a, sum, found, ri, rj),
    invariant: found == has_two_sum_before_i(a, sum, i),
  }
  if found {
    Some((ri, rj))
  } else {
    None
  }
}

///|
#requires(nonnegative(sum))
#requires(nonnegative_entries(a))
#ensures(two_sum_result_ok(a, sum, result))
pub fn one_loop_positive(a : FixedArray[Int], sum : Int) -> (Int, Int)? {
  let seen = FixedArray::make(sum + 1, 0)
  let (found, ri, rj) = for i = 0, found = false, ri = 0, rj = 0; i < a.length(); {
    if found {
      continue i + 1, true, ri, rj
    } else if a[i] <= sum {
      seen[a[i]] = i + 1
      let complement = sum - a[i]
      if complement == a[i] {
        let hit_i = i
        continue i + 1, true, hit_i, hit_i
      } else {
        let j = seen[complement]
        let hit = j != 0
        let next_ri = if hit { i } else { ri }
        let next_rj = if hit { j - 1 } else { rj }
        continue i + 1, hit, next_ri, next_rj
      }
    } else {
      continue i + 1, false, ri, rj
    }
  } nobreak {
    (found, ri, rj)
  } where {
    invariant: 0 <= i,
    invariant: i <= a.length(),
    invariant: seen.length() == sum + 1,
    invariant: witness_state_ok(a, sum, found, ri, rj),
    invariant: found == has_two_sum_in_prefix(a, sum, i),
    invariant: found || seen_complete(seen, a, i),
    invariant: found || seen_sound(seen, a, i),
  }
  if found {
    Some((ri, rj))
  } else {
    None
  }
}

///|
#requires(nonnegative(sum))
#requires(nonnegative_entries(a))
#ensures(two_loop_exists_ok(a, sum, result))
pub fn one_loop_positive_exists(a : FixedArray[Int], sum : Int) -> Bool {
  let seen = FixedArray::make(sum + 1, 0)
  for i = 0, found = false; i < a.length(); {
    if found {
      continue i + 1, true
    } else if a[i] <= sum {
      seen[a[i]] = i + 1
      let hit = seen[sum - a[i]] != 0
      continue i + 1, hit
    } else {
      continue i + 1, false
    }
  } nobreak {
    found
  } where {
    invariant: 0 <= i,
    invariant: i <= a.length(),
    invariant: seen.length() == sum + 1,
    invariant: found == has_two_sum_in_prefix(a, sum, i),
    invariant: found || seen_complete(seen, a, i),
    invariant: found || seen_sound(seen, a, i),
  }
}
