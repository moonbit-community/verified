///|
pub struct QC {
  block : Int
  round : Int
  signers : UInt
} derive(Eq, Debug)

///|
pub fn make_qc(block : Int, round : Int, signers : UInt) -> QC {
  { block, round, signers }
}

///|
fn member_at(
  bitmap : UInt,
  idx : Int,
) -> Bool where {
  proof_require: valid_member_idx(idx),
  proof_ensure: result => result == member_at_value(bitmap, idx),
} {
  let shifted = @bitmap32.uint_lsr(bitmap, idx)
  let result = @bitmap32.uint_bit0(shifted)
  proof_assert result == member_at_value(bitmap, idx)
  result
}

///|
fn union_count(
  left : UInt,
  right : UInt,
  n : Int,
) -> Int where {
  proof_require: valid_validator_count(n),
  proof_ensure: result => result == union_count_upto(left, right, n),
} {
  for i = 0, acc = 0; i < n; {
    proof_assert valid_member_idx(i)
    let in_left = member_at(left, i)
    let in_right = member_at(right, i)
    let next_acc = if in_left || in_right { acc + 1 } else { acc }
    proof_assert next_acc == union_count_upto(left, right, i + 1)
    continue i + 1, next_acc
  } nobreak {
    acc
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: acc == union_count_upto(left, right, i),
  }
}

///|
fn count_partition(
  left : UInt,
  right : UInt,
  n : Int,
) -> Unit where {
  proof_require: valid_validator_count(n),
  proof_ensure: signer_count_upto(left, n) + signer_count_upto(right, n) ==
  shared_count_upto(left, right, n) + union_count_upto(left, right, n),
  proof_ensure: union_count_upto(left, right, n) <= n,
} {
  for i = 0, left_count = 0, right_count = 0, shared = 0, union = 0; i < n; {
    proof_assert valid_member_idx(i)
    let in_left = member_at(left, i)
    let in_right = member_at(right, i)
    let next_left = if in_left { left_count + 1 } else { left_count }
    let next_right = if in_right { right_count + 1 } else { right_count }
    let next_shared = if in_left && in_right { shared + 1 } else { shared }
    let next_union = if in_left || in_right { union + 1 } else { union }
    proof_assert next_left == signer_count_upto(left, i + 1)
    proof_assert next_right == signer_count_upto(right, i + 1)
    proof_assert next_shared == shared_count_upto(left, right, i + 1)
    proof_assert next_union == union_count_upto(left, right, i + 1)
    proof_assert next_left + next_right == next_shared + next_union
    proof_assert next_union <= i + 1
    continue i + 1, next_left, next_right, next_shared, next_union
  } nobreak {
    ()
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: left_count == signer_count_upto(left, i),
    proof_invariant: right_count == signer_count_upto(right, i),
    proof_invariant: shared == shared_count_upto(left, right, i),
    proof_invariant: union == union_count_upto(left, right, i),
    proof_invariant: left_count + right_count == shared + union,
    proof_invariant: union <= i,
  }
}

///|
pub fn signer_count(
  bitmap : UInt,
  n : Int,
) -> Int where {
  proof_require: valid_validator_count(n),
  proof_ensure: result => signer_count_post(bitmap, n, result),
} {
  for i = 0, acc = 0; i < n; {
    proof_assert valid_member_idx(i)
    let present = member_at(bitmap, i)
    let next_acc = if present { acc + 1 } else { acc }
    proof_assert next_acc == signer_count_upto(bitmap, i + 1)
    continue i + 1, next_acc
  } nobreak {
    acc
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: acc == signer_count_upto(bitmap, i),
  }
}

///|
pub fn shared_count(
  left : UInt,
  right : UInt,
  n : Int,
) -> Int where {
  proof_require: valid_validator_count(n),
  proof_ensure: result => shared_count_post(left, right, n, result),
} {
  for i = 0, acc = 0; i < n; {
    proof_assert valid_member_idx(i)
    let in_left = member_at(left, i)
    let in_right = member_at(right, i)
    let next_acc = if in_left && in_right { acc + 1 } else { acc }
    proof_assert next_acc == shared_count_upto(left, right, i + 1)
    continue i + 1, next_acc
  } nobreak {
    acc
  } where {
    proof_invariant: 0 <= i,
    proof_invariant: i <= n,
    proof_invariant: acc == shared_count_upto(left, right, i),
  }
}

///|
pub fn has_quorum(
  bitmap : UInt,
  n : Int,
  f : Int,
) -> Bool where {
  proof_require: validator_params(n, f),
  proof_ensure: result => has_quorum_post(bitmap, n, f, result),
} {
  let count = signer_count(bitmap, n)
  let result = count >= 2 * f + 1
  proof_assert has_quorum_post(bitmap, n, f, result)
  result
}

///|
pub fn conflicting(
  a : QC,
  b : QC,
) -> Bool where {
  proof_ensure: result => conflicting_post(a, b, result),
} {
  let result = a.round == b.round && a.block != b.block
  proof_assert conflicting_post(a, b, result)
  result
}

///|
pub fn slashable_overlap(
  a : QC,
  b : QC,
  n : Int,
  _f : Int,
) -> Int where {
  proof_require: validator_params(n, _f),
  proof_require: conflicting_qcs(a, b),
  proof_require: signer_count_upto(a.signers, n) >= 2 * _f + 1,
  proof_require: signer_count_upto(b.signers, n) >= 2 * _f + 1,
  proof_ensure: result => slashable_overlap_post(a, b, n, _f, result),
} {
  let _left = signer_count(a.signers, n)
  let _right = signer_count(b.signers, n)
  let shared = shared_count(a.signers, b.signers, n)
  let _union = union_count(a.signers, b.signers, n)
  count_partition(a.signers, b.signers, n)
  proof_assert _left == signer_count_upto(a.signers, n)
  proof_assert _right == signer_count_upto(b.signers, n)
  proof_assert shared == shared_count_upto(a.signers, b.signers, n)
  proof_assert _union == union_count_upto(a.signers, b.signers, n)
  proof_assert 2 * _f + 1 <= _left
  proof_assert 2 * _f + 1 <= _right
  proof_assert 4 * _f + 2 <= _left + _right
  proof_assert shared + _union == _left + _right
  proof_assert 4 * _f + 2 <= shared + _union
  proof_assert _union <= n
  proof_assert 4 * _f + 2 <= shared + n
  proof_assert n == 3 * _f + 1
  proof_assert _f + 1 <= shared
  proof_assert slashable_overlap_post(a, b, n, _f, shared)
  shared
}

///|
pub fn slashable(
  a : QC,
  b : QC,
  n : Int,
  f : Int,
) -> Bool where {
  proof_require: validator_params(n, f),
  proof_ensure: result => slashable_post(a, b, n, f, result),
} {
  let result = conflicting(a, b) &&
    has_quorum(a.signers, n, f) &&
    has_quorum(b.signers, n, f) &&
    shared_count(a.signers, b.signers, n) >= f + 1
  proof_assert slashable_post(a, b, n, f, result)
  result
}
