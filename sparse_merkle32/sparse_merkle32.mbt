///|
pub enum Tree {
  Zero(Int)
  Leaf(Int)
  Branch(Tree, Tree)
} derive(Eq, Debug)

///|
/// This package uses the same deterministic hash combiner as `merkle_path32`.
#proof_pure
fn hash_pair(left : Int, right : Int) -> Int {
  (left * 17 + right * 31 + 7) % 1_000_003
}

///|
fn bit_at(
  key : UInt,
  idx : Int,
) -> Bool where {
  proof_require: valid_member_idx(idx),
  proof_ensure: result => result == bit_at_value(key, idx),
} {
  let shifted = @bitmap32.uint_lsr(key, idx)
  let result = @bitmap32.uint_bit0(shifted)
  proof_assert result == bit_at_value(key, idx)
  result
}

///|
fn zero_root(remaining : Int) -> Int {
  if remaining <= 0 {
    0
  } else {
    let child = zero_root(remaining - 1)
    hash_pair(child, child)
  }
}

///|
fn tree_height(
  tree : Tree,
) -> Int where {
  proof_decrease: tree,
  proof_require: tree_inv(tree),
  proof_ensure: result => result == height_value(tree),
} {
  match tree {
    Zero(remaining) => remaining
    Leaf(_value) => 0
    Branch(left, _) => 1 + tree_height(left)
  }
}

///|
pub fn empty() -> Tree where { proof_ensure: result => empty_post(result) } {
  let result = Zero(32)
  proof_assert empty_post(result)
  result
}

///|
fn root_subtree(tree : Tree) -> Int {
  match tree {
    Zero(remaining) => zero_root(remaining)
    Leaf(value) => value
    Branch(left, right) => {
      let left_root = root_subtree(left)
      let right_root = root_subtree(right)
      hash_pair(left_root, right_root)
    }
  }
}

///|
pub fn root(tree : Tree) -> Int {
  root_subtree(tree)
}

///|
fn lookup_subtree(
  tree : Tree,
  key : UInt,
) -> Int where {
  proof_decrease: height_value(tree),
  proof_require: tree_inv(tree),
  proof_ensure: result => lookup_rel(tree, key, result),
} {
  match tree {
    Zero(_remaining) => {
      proof_assert lookup_rel(tree, key, 0)
      0
    }
    Leaf(value) => {
      proof_assert lookup_rel(tree, key, value)
      value
    }
    Branch(left, right) => {
      let left_height = tree_height(left)
      proof_assert left_height == height_value(left)
      proof_assert 0 <= left_height
      proof_assert 1 + left_height <= 32
      let depth = 31 - left_height
      proof_assert valid_member_idx(depth)
      let bit = bit_at(key, depth)
      if bit {
        let result = lookup_subtree(right, key)
        proof_assert bit == bit_at_value(key, depth)
        proof_assert lookup_rel(tree, key, result)
        result
      } else {
        let result = lookup_subtree(left, key)
        proof_assert bit == bit_at_value(key, depth)
        proof_assert lookup_rel(tree, key, result)
        result
      }
    }
  }
}

///|
pub fn lookup(
  tree : Tree,
  key : UInt,
) -> Int where {
  proof_require: full_tree_inv(tree),
  proof_ensure: result => lookup_post(tree, key, result),
} {
  let result = lookup_subtree(tree, key)
  proof_assert lookup_post(tree, key, result)
  result
}

///|
fn update_subtree(
  tree : Tree,
  key : UInt,
  value : Int,
) -> Tree where {
  proof_decrease: height_value(tree),
  proof_require: tree_inv(tree),
  proof_ensure: result => update_subtree_post(tree, key, value, result),
} {
  match tree {
    Zero(remaining) =>
      if remaining == 0 {
        let result = Leaf(value)
        proof_assert tree_inv(result)
        proof_assert height_value(result) == height_value(tree)
        proof_assert lookup_rel(result, key, value)
        proof_assert update_subtree_post(tree, key, value, result)
        result
      } else {
        proof_assert 0 < remaining
        let child = Zero(remaining - 1)
        proof_assert tree_inv(child)
        let depth = 32 - remaining
        proof_assert 0 <= depth
        proof_assert depth < 32
        let bit = bit_at(key, depth)
        if bit {
          let updated_right = update_subtree(child, key, value)
          let result = Branch(child, updated_right)
          proof_assert tree_inv(result)
          proof_assert height_value(result) == height_value(tree)
          proof_assert bit == bit_at_value(key, depth)
          proof_assert lookup_rel(result, key, value)
          proof_assert update_subtree_post(tree, key, value, result)
          result
        } else {
          let updated_left = update_subtree(child, key, value)
          let result = Branch(updated_left, child)
          proof_assert tree_inv(result)
          proof_assert height_value(result) == height_value(tree)
          proof_assert bit == bit_at_value(key, depth)
          proof_assert lookup_rel(result, key, value)
          proof_assert update_subtree_post(tree, key, value, result)
          result
        }
      }
    Leaf(_old_value) => {
      let result = Leaf(value)
      proof_assert tree_inv(result)
      proof_assert height_value(result) == height_value(tree)
      proof_assert lookup_rel(result, key, value)
      proof_assert update_subtree_post(tree, key, value, result)
      result
    }
    Branch(left, right) => {
      let left_height = tree_height(left)
      proof_assert left_height == height_value(left)
      proof_assert 0 <= left_height
      proof_assert 1 + left_height <= 32
      let depth = 31 - left_height
      proof_assert valid_member_idx(depth)
      let bit = bit_at(key, depth)
      if bit {
        let updated_right = update_subtree(right, key, value)
        let result = Branch(left, updated_right)
        proof_assert tree_inv(result)
        proof_assert height_value(result) == height_value(tree)
        proof_assert bit == bit_at_value(key, depth)
        proof_assert lookup_rel(result, key, value)
        proof_assert update_subtree_post(tree, key, value, result)
        result
      } else {
        let updated_left = update_subtree(left, key, value)
        let result = Branch(updated_left, right)
        proof_assert tree_inv(result)
        proof_assert height_value(result) == height_value(tree)
        proof_assert bit == bit_at_value(key, depth)
        proof_assert lookup_rel(result, key, value)
        proof_assert update_subtree_post(tree, key, value, result)
        result
      }
    }
  }
}

///|
pub fn update(
  tree : Tree,
  key : UInt,
  value : Int,
) -> Tree where {
  proof_require: full_tree_inv(tree),
  proof_ensure: result => update_post(tree, key, value, result),
} {
  let result = update_subtree(tree, key, value)
  proof_assert full_tree_inv(result)
  proof_assert lookup_rel(result, key, value)
  proof_assert update_post(tree, key, value, result)
  result
}
