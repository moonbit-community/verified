///|
fn build_skip_table(
  needle : Bytes,
  needle_len : Int,
) -> FixedArray[Int] where {
  proof_require: bytes_len_ok(needle, needle_len),
  proof_require: needle_len > 0,
  proof_ensure: result => skip_table_ok(result, needle),
} {
  let skip = FixedArray::make(256, needle_len)
  // After processing prefix [0, i), `skip` stores the smallest safe shift
  // witnessed so far for each byte that appears in that prefix.
  for i = 0; i < needle_len - 1; {
    proof_assert 0 <= i
    proof_assert i < needle_len - 1
    proof_assert bytes_get_int_pre(needle, i)
    let current = needle[i].to_int()
    proof_assert 0 <= current
    proof_assert current < 256
    proof_assert 1 <= needle_len - 1 - i
    proof_assert needle_len - 1 - i <= needle_len
    skip[current] = needle_len - 1 - i
    continue i + 1
  } nobreak {
    proof_assert i == needle_len - 1
    proof_assert i == bytes_length(needle) - 1
    proof_assert skip_table_prefix_ok(skip, needle, i)
    proof_assert ∀ c : Int,
      ∀ s : Int,
        0 <= c && c < 256 && 1 <= s && s < skip[c] →
        byte_value(needle, bytes_length(needle) - 1 - s) != c
    proof_assert skip_table_ok(skip, needle)
    skip
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= needle_len - 1,
    proof_invariant: bytes_len_ok(needle, needle_len),
    proof_invariant: skip_table_prefix_ok(skip, needle, i),
  }
}

///|
fn matches_at(
  haystack : Bytes,
  needle : Bytes,
  offset : Int,
  needle_len : Int,
) -> Bool where {
  proof_require: bytes_len_ok(needle, needle_len),
  proof_require: valid_offset(haystack, needle, offset),
  proof_ensure: result => matches_at_ok(haystack, needle, offset, result),
} {
  for j = 0, mismatch = -1; j < needle_len; {
    proof_assert j < needle_len
    proof_assert needle_len == bytes_length(needle)
    proof_assert j < bytes_length(needle)
    proof_assert 0 <= j
    proof_assert bytes_get_int_pre(needle, j)
    proof_assert offset + j < bytes_length(haystack)
    proof_assert bytes_get_int_pre(haystack, offset + j)
    let new_mismatch = if mismatch == -1 &&
      haystack[offset + j].to_int() != needle[j].to_int() {
      j
    } else {
      mismatch
    }
    continue j + 1, new_mismatch
  } nobreak {
    proof_assert needle_len == bytes_length(needle)
    proof_assert needle_len <= j
    proof_assert j == needle_len
    proof_assert j == bytes_length(needle)
    // The loop exits with either a witness mismatch or a fully matched prefix.
    if mismatch == -1 {
      proof_assert mismatch != -1 || matched_prefix(haystack, needle, offset, j)
      proof_assert matched_prefix(haystack, needle, offset, j)
      proof_assert matched_prefix(
        haystack,
        needle,
        offset,
        bytes_length(needle),
      )
      proof_assert match_at(haystack, needle, offset)
    } else {
      proof_assert 0 <= mismatch
      proof_assert mismatch < j
      proof_assert mismatch < bytes_length(needle)
      proof_assert byte_value(haystack, offset + mismatch) !=
        byte_value(needle, mismatch)
      proof_assert !match_at(haystack, needle, offset)
    }
    mismatch == -1
  } where {
    proof_invariant: 0 <= j,
    proof_invariant: mismatch_scan_inv(haystack, needle, offset, j, mismatch),
    proof_invariant: mismatch == -1 || (0 <= mismatch && mismatch < j),
    proof_invariant: mismatch != -1 ||
    matched_prefix(haystack, needle, offset, j),
    proof_invariant: j <= needle_len,
    proof_invariant: bytes_len_ok(needle, needle_len),
  }
}

///|
pub fn boyer_moore_horspool_find(
  haystack : Bytes,
  needle : Bytes,
) -> Int? where {
  proof_ensure: result => search_ok(haystack, needle, result),
} {
  let haystack_len = haystack.length()
  let needle_len = needle.length()
  proof_assert bytes_len_ok(haystack, haystack_len)
  proof_assert bytes_len_ok(needle, needle_len)
  if needle_len <= 0 {
    Some(0)
  } else if haystack_len < needle_len {
    None
  } else {
    let skip = build_skip_table(needle, needle_len)
    for i = 0; i < haystack_len - needle_len + 1; {
      if matches_at(haystack, needle, i, needle_len) {
        proof_assert search_ok(haystack, needle, Some(i))
        break Some(i)
      }
      proof_assert bytes_get_int_pre(haystack, i + needle_len - 1)
      let last = haystack[i + needle_len - 1].to_int()
      proof_assert 0 <= last
      proof_assert last < 256
      let shift = skip[last]
      proof_assert !match_at(haystack, needle, i)
      proof_assert 1 <= shift
      proof_assert shift <= needle_len
      proof_assert skip_step_pre(haystack, needle, skip, i, last, shift)
      proof_assert no_match_before(haystack, needle, i + shift)
      continue i + shift
    } nobreak {
      None
    } where {
      proof_invariant: 0 <= i,
      proof_invariant: i <= haystack_len,
      proof_invariant: no_match_before(haystack, needle, i),
      proof_invariant: skip_table_ok(skip, needle),
      proof_invariant: bytes_len_ok(haystack, haystack_len),
      proof_invariant: bytes_len_ok(needle, needle_len),
      proof_invariant: needle_len > 0,
      proof_yield: res => search_ok(haystack, needle, res),
      proof_reasoning: (
        #| The scan invariant records that every valid start position strictly before `i`
        #| has already been ruled out.
        #|
        #| If `matches_at` succeeds we yield the current start, and the invariant
        #| gives minimality. Otherwise, BMH shifts by `skip[last]`, where `last`
        #| is the byte aligned with the final needle position at the current window.
        #|
        #| The skip-table contract states that for every `1 <= s < skip[last]`,
        #| the needle byte at position `needle_len - 1 - s` is different from `last`.
        #| Any hypothetical match beginning at `i + s` would force that very needle
        #| position to equal `last`, contradiction. So every valid start in
        #| `[i, i + skip[last])` is not a match, which re-establishes
        #| `no_match_before` after the jump.
      ),
    }
  }
}
