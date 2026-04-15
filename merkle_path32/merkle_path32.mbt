///|
pub enum Path {
  Nil
  Cons(Int, Path)
} derive(Eq, Debug)

///|
/// This is a deterministic binary combiner for proof purposes, not a real
/// cryptographic hash. The package proves exact path semantics against this
/// combiner shape; it does not attempt a security theorem such as collision
/// resistance.
#proof_pure
fn hash_pair(left : Int, right : Int) -> Int {
  (left * 17 + right * 31 + 7) % 1_000_003
}

///|
/// `step_hash` makes the one-step branch choice explicit in a pure helper so
/// both executable code and the proof model can share the same transition.
#proof_pure
fn step_hash(bit : Bool, acc : Int, sibling : Int) -> Int {
  if bit {
    hash_pair(sibling, acc)
  } else {
    hash_pair(acc, sibling)
  }
}

///|
/// `bit_at` is the runtime/proof bridge for the path direction bit at `depth`.
/// The implementation uses the existing verified bitmap/bitvector bridge so the
/// proof layer sees the same bit as the executable code.
fn bit_at(
  key : UInt,
  depth : Int,
) -> Bool where {
  proof_require: valid_depth(depth),
  proof_ensure: result => result == bit_at_value(key, depth),
} {
  let shifted = @bitmap32.uint_lsr(key, depth)
  let result = @bitmap32.uint_bit0(shifted)
  proof_assert result == bit_at_value(key, depth)
  result
}

///|
fn path_len_nonneg(
  path : Path,
) -> Unit where {
  proof_decrease: path,
  proof_ensure: 0 <= path_len(path),
} {
  match path {
    Nil => ()
    Cons(_, rest) => path_len_nonneg(rest)
  }
}

///|
fn nonempty_prefix_valid_depth(
  _depth : Int,
  _path : Path,
) -> Unit where {
  proof_require: valid_depth_prefix(_depth, _path),
  proof_require: 0 < path_len(_path),
  proof_ensure: valid_depth(_depth),
} {
  proof_assert valid_depth(_depth)
}

///|
/// `compute_root_from` is the core authenticated-path fold. `depth` records the
/// next key bit to inspect, and `acc` is the subtree hash already accumulated
/// from the leaf upward.
pub fn compute_root_from(
  key : UInt,
  depth : Int,
  acc : Int,
  path : Path,
) -> Int where {
  proof_decrease: path_len(path),
  proof_require: valid_depth_prefix(depth, path),
  proof_ensure: result => root_from_post(key, depth, acc, path, result),
} {
  match path {
    Nil => {
      let empty = Nil
      proof_assert path == empty
      proof_assert root_from_post(key, depth, acc, empty, acc)
      acc
    }
    Cons(sibling, rest) => {
      proof_assert valid_depth_prefix(depth, Cons(sibling, rest))
      proof_assert path_len(Cons(sibling, rest)) == 1 + path_len(rest)
      path_len_nonneg(rest)
      proof_assert 0 < 1 + path_len(rest)
      nonempty_prefix_valid_depth(depth, Cons(sibling, rest))
      proof_assert valid_depth(depth)
      let bit = bit_at(key, depth)
      let next = step_hash(bit, acc, sibling)
      proof_assert path_len(rest) < path_len(Cons(sibling, rest))
      proof_assert valid_depth_prefix(depth + 1, rest)
      let result = compute_root_from(key, depth + 1, next, rest)
      proof_assert bit == bit_at_value(key, depth)
      proof_assert root_from_post(key, depth, acc, Cons(sibling, rest), result)
      result
    }
  }
}

///|
/// A 32-step path corresponds to a full binary Merkle authentication path over
/// a 32-bit key space.
pub fn compute_root(
  key : UInt,
  leaf : Int,
  path : Path,
) -> Int where {
  proof_require: full_path(path),
  proof_ensure: result => compute_root_post(key, leaf, path, result),
} {
  proof_assert valid_depth_prefix(0, path)
  let result = compute_root_from(key, 0, leaf, path)
  proof_assert compute_root_post(key, leaf, path, result)
  result
}

///|
/// Verification is exact recomputation: a proof is accepted iff the claimed
/// root matches the recomputed root.
pub fn verify(
  root : Int,
  key : UInt,
  leaf : Int,
  path : Path,
) -> Bool where {
  proof_require: full_path(path),
  proof_ensure: result => verify_post(root, key, leaf, path, result),
} {
  let recomputed = compute_root(key, leaf, path)
  let result = root == recomputed
  proof_assert compute_root_post(key, leaf, path, recomputed)
  proof_assert verify_post(root, key, leaf, path, result)
  result
}
