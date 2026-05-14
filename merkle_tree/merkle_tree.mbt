///|
pub enum Direction {
  Left
  Right
} derive(Debug)

///|
pub enum MerkleProof {
  Done
  Step(Direction, Int, MerkleProof)
} derive(Debug)

///|
enum MerkleNode {
  Leaf(Int, Int)
  Node(MerkleNode, MerkleNode, Int)
} derive(Debug)

///|
pub struct MerkleTree {
  inner : MerkleNode
} derive(Debug)

///|
fn hash_leaf(
  data : Int,
) -> Int where {
  proof_axiomatized: true,
  proof_ensure: result => result == leaf_hash_model(data),
} {
  data * 2 + 1
}

///|
fn hash_node(
  left : Int,
  right : Int,
) -> Int where {
  proof_axiomatized: true,
  proof_ensure: result => result == node_hash_model(left, right),
} {
  left * 131 + right * 17 + 3
}

///|
fn prove_tree_size_positive(
  node : MerkleNode,
) -> Unit where {
  proof_decrease: node,
  proof_ensure: 0 < tree_size(node),
} {
  match node {
    Leaf(_data, _hash) => ()
    Node(left, right, _hash) => {
      prove_tree_size_positive(left)
      prove_tree_size_positive(right)
    }
  }
}

///|
fn prove_left_child_size_decrease(
  left : MerkleNode,
  right : MerkleNode,
  hash : Int,
) -> Unit where {
  proof_ensure: tree_size(left) < tree_size(Node(left, right, hash)),
} {
  prove_tree_size_positive(right)
}

///|
fn prove_right_child_size_decrease(
  left : MerkleNode,
  right : MerkleNode,
  hash : Int,
) -> Unit where {
  proof_ensure: tree_size(right) < tree_size(Node(left, right, hash)),
} {
  prove_tree_size_positive(left)
}

///|
fn prove_proof_size_positive(
  proof : MerkleProof,
) -> Unit where {
  proof_decrease: proof,
  proof_ensure: 0 < proof_size(proof),
} {
  match proof {
    Done => ()
    Step(_direction, _sibling, rest) => prove_proof_size_positive(rest)
  }
}

///|
pub fn singleton(
  data : Int,
) -> MerkleTree where {
  proof_ensure: result => singleton_post(data, result),
} {
  let h = hash_leaf(data)
  let result = { inner: Leaf(data, h) }
  proof_assert singleton_post(data, result)
  result
}

///|
pub fn combine(
  left : MerkleTree,
  right : MerkleTree,
) -> MerkleTree where {
  proof_require: tree_inv(left),
  proof_require: tree_inv(right),
  proof_ensure: result => combine_post(left, right, result),
} {
  let left_root = root(left)
  let right_root = root(right)
  let h = hash_node(left_root, right_root)
  let result = { inner: Node(left.inner, right.inner, h) }
  proof_assert left_root == root_hash(left.inner)
  proof_assert right_root == root_hash(right.inner)
  proof_assert merkle_inv(result.inner)
  proof_assert tree_size(result.inner) ==
    tree_size(left.inner) + tree_size(right.inner)
  proof_assert root_hash(result.inner) ==
    node_hash_model(root_hash(left.inner), root_hash(right.inner))
  proof_assert combine_post(left, right, result)
  result
}

///|
pub fn root(
  tree : MerkleTree,
) -> Int where {
  proof_ensure: result => root_post(tree, result),
} {
  match tree.inner {
    Leaf(_data, hash) => hash
    Node(_left, _right, hash) => hash
  }
}

///|
pub fn size(
  tree : MerkleTree,
) -> Int where {
  proof_ensure: result => size_post(tree, result),
} {
  node_size(tree.inner)
}

///|
fn node_size(
  node : MerkleNode,
) -> Int where {
  proof_decrease: tree_size(node),
  proof_ensure: result => result == tree_size(node),
} {
  prove_tree_size_positive(node)
  match node {
    Leaf(_data, _hash) => 1
    Node(left, right, hash) => {
      prove_left_child_size_decrease(left, right, hash)
      prove_right_child_size_decrease(left, right, hash)
      node_size(left) + node_size(right)
    }
  }
}

///|
pub fn leaf(
  tree : MerkleTree,
  index : Int,
) -> Int where {
  proof_require: valid_tree_index(tree, index),
  proof_ensure: result => leaf_post(tree, index, result),
} {
  let result = leaf_node(tree.inner, index)
  proof_assert leaf_post(tree, index, result)
  result
}

///|
fn leaf_node(
  node : MerkleNode,
  index : Int,
) -> Int where {
  proof_decrease: tree_size(node),
  proof_require: merkle_inv(node),
  proof_require: valid_index(node, index),
  proof_ensure: result => result == leaf_at(node, index),
} {
  match node {
    Leaf(data, _hash) => {
      proof_assert index == 0
      data
    }
    Node(left, right, hash) => {
      prove_left_child_size_decrease(left, right, hash)
      prove_right_child_size_decrease(left, right, hash)
      proof_assert merkle_inv(left)
      proof_assert merkle_inv(right)
      let left_size = node_size(left)
      proof_assert left_size == tree_size(left)
      if index < left_size {
        proof_assert valid_index(left, index)
        let result = leaf_node(left, index)
        proof_assert result == leaf_at(node, index)
        result
      } else {
        let right_index = index - left_size
        proof_assert valid_index(right, right_index)
        let result = leaf_node(right, right_index)
        proof_assert result == leaf_at(node, index)
        result
      }
    }
  }
}

///|
pub fn verify_proof(
  data : Int,
  proof : MerkleProof,
  expected_root : Int,
) -> Bool where {
  proof_ensure: result => verify_proof_post(data, proof, expected_root, result),
} {
  let actual = replay_proof(data, proof)
  let result = actual == expected_root
  proof_assert actual == replay_hash(data, proof)
  proof_assert result == (replay_hash(data, proof) == expected_root)
  proof_assert verify_proof_post(data, proof, expected_root, result)
  result
}

///|
fn replay_proof(
  data : Int,
  proof : MerkleProof,
) -> Int where {
  proof_decrease: proof_size(proof),
  proof_ensure: result => result == replay_hash(data, proof),
} {
  prove_proof_size_positive(proof)
  match proof {
    Done => {
      let result = hash_leaf(data)
      proof_assert result == replay_hash(data, proof)
      result
    }
    Step(direction, sibling, rest) => {
      let child = replay_proof(data, rest)
      match direction {
        Left => {
          let result = hash_node(child, sibling)
          proof_assert child == replay_hash(data, rest)
          proof_assert result == replay_hash(data, proof)
          result
        }
        Right => {
          let result = hash_node(sibling, child)
          proof_assert child == replay_hash(data, rest)
          proof_assert result == replay_hash(data, proof)
          result
        }
      }
    }
  }
}

///|
pub fn make_proof(
  tree : MerkleTree,
  index : Int,
) -> MerkleProof? where {
  proof_require: valid_tree_index(tree, index),
  proof_ensure: result => make_tree_proof_post(tree, index, result),
} {
  let result = make_proof_node(tree.inner, index)
  proof_assert make_tree_proof_post(tree, index, result)
  result
}

///|
fn make_proof_node(
  node : MerkleNode,
  index : Int,
) -> MerkleProof? where {
  proof_decrease: tree_size(node),
  proof_require: merkle_inv(node),
  proof_require: valid_index(node, index),
  proof_ensure: result => make_proof_post(node, index, result),
} {
  match node {
    Leaf(_data, _hash) => {
      let result = Some(Done)
      proof_assert index == 0
      proof_assert make_proof_post(node, index, result)
      result
    }
    Node(left, right, hash) => {
      prove_left_child_size_decrease(left, right, hash)
      prove_right_child_size_decrease(left, right, hash)
      proof_assert merkle_inv(left)
      proof_assert merkle_inv(right)
      proof_assert root_hash(node) == hash
      proof_assert hash == node_hash_model(root_hash(left), root_hash(right))
      let left_size = node_size(left)
      proof_assert left_size == tree_size(left)
      if index < left_size {
        proof_assert valid_index(left, index)
        let child = make_proof_node(left, index)
        match child {
          Some(rest) => {
            let right_root = node_root(right)
            proof_assert right_root == root_hash(right)
            let result = Some(Step(Left, right_root, rest))
            proof_assert replay_hash(leaf_at(left, index), rest) ==
              root_hash(left)
            proof_assert leaf_at(node, index) == leaf_at(left, index)
            proof_assert replay_hash(
                leaf_at(node, index),
                Step(Left, right_root, rest),
              ) ==
              root_hash(node)
            proof_assert make_proof_post(node, index, result)
            result
          }
          None => {
            proof_assert false
            None
          }
        }
      } else {
        let right_index = index - left_size
        proof_assert valid_index(right, right_index)
        let child = make_proof_node(right, right_index)
        match child {
          Some(rest) => {
            let left_root = node_root(left)
            proof_assert left_root == root_hash(left)
            let result = Some(Step(Right, left_root, rest))
            proof_assert replay_hash(leaf_at(right, right_index), rest) ==
              root_hash(right)
            proof_assert leaf_at(node, index) == leaf_at(right, right_index)
            proof_assert replay_hash(
                leaf_at(node, index),
                Step(Right, left_root, rest),
              ) ==
              root_hash(node)
            proof_assert make_proof_post(node, index, result)
            result
          }
          None => {
            proof_assert false
            None
          }
        }
      }
    }
  }
}

///|
fn node_root(
  node : MerkleNode,
) -> Int where {
  proof_ensure: result => result == root_hash(node),
} {
  match node {
    Leaf(_data, hash) => hash
    Node(_left, _right, hash) => hash
  }
}

///|
pub fn generated_proof_verifies(
  tree : MerkleTree,
  index : Int,
) -> Bool where {
  proof_require: valid_tree_index(tree, index),
  proof_ensure: result => generated_proof_verifies_post(tree, index, result),
} {
  let proof = make_proof(tree, index)
  match proof {
    Some(path) => {
      let data = leaf(tree, index)
      let expected = root(tree)
      let result = verify_proof(data, path, expected)
      proof_assert data == leaf_at(tree.inner, index)
      proof_assert expected == root_hash(tree.inner)
      proof_assert replay_hash(data, path) == root_hash(tree.inner)
      proof_assert result == true
      proof_assert generated_proof_verifies_post(tree, index, result)
      result
    }
    None => {
      proof_assert false
      false
    }
  }
}
