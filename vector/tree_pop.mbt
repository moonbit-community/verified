///|
fn[T] Tree::last_leaf_elements(
  self : Tree[T],
  shift : Int,
) -> ReadOnlyArray[T] where {
  proof_axiomatized: true,
  proof_require: tree_inv(self, root_level(shift)),
  proof_require: @mathint.int_model(0) <
  tree_model(self, root_level(shift)).length(),
  proof_ensure: result => last_leaf_elements_post(self, shift, result),
} {
  match self {
    Leaf(leaf) => leaf
    Node(children, _) =>
      children[children.length() - 1].last_leaf_elements(shift - num_bits)
    Empty => abort("Empty tree has no last leaf")
  }
}

///|
fn[T] Tree::pop_rightmost_leaf(
  self : Tree[T],
  shift : Int,
) -> Tree[T] where {
  proof_axiomatized: true,
  proof_require: tree_inv(self, root_level(shift)),
  proof_require: @mathint.int_model(0) <
  tree_model(self, root_level(shift)).length(),
  proof_ensure: result => pop_rightmost_leaf_post(self, shift, result),
} {
  match self {
    Empty => Empty
    Leaf(_) => Empty
    Node(children, _) => {
      let last_index = children.length() - 1
      let new_last = children[last_index].pop_rightmost_leaf(shift - num_bits)
      match new_last {
        Empty =>
          if last_index == 0 {
            Empty
          } else {
            let new_children = immutable_slice(children, 0, last_index)
            Node(new_children, compute_sizes(new_children, shift - num_bits))
          }
        _ => {
          let new_children = immutable_set(children, last_index, new_last)
          Node(new_children, compute_sizes(new_children, shift - num_bits))
        }
      }
    }
  }
}

///|
fn[T] Tree::shrink_top(
  self : Tree[T],
  shift : Int,
) -> (Tree[T], Int) where {
  proof_axiomatized: true,
  proof_require: vector_tree_inv(self, root_level(shift)),
  proof_ensure: result => shrink_top_post(self, shift, result),
} {
  // `moon prove` does not currently support this cursor-style loop in
  // untrusted contracted bodies. A recursive version lowers, but then runs
  // into child model transport obligations for single-child nodes.
  let mut current_shift = shift
  for tree = self {
    match tree {
      Node(children, _) if current_shift > 0 && children.length() == 1 => {
        current_shift -= num_bits
        continue children[0]
      }
      Empty => break (Empty, 0)
      current => break (current, current_shift)
    }
  }
}
