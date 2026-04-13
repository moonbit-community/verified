///|
fn[T : Eq] Tree::get(
  self : Tree[T],
  index : Int,
  shift : Int,
) -> T where {
  proof_axiomatized: true,
  proof_require: tree_inv(self, root_level(shift)),
  proof_require: tree_valid_index_model(self, shift, index),
  proof_ensure: result => tree_get_post(self, shift, index, result),
} {
  match self {
    Leaf(leaf) => leaf[index]
    Node(children, Some(sizes)) => {
      let branch_index = get_branch_index(sizes, index)
      let sub_index = if branch_index == 0 {
        index
      } else {
        index - sizes[branch_index - 1]
      }
      children[branch_index].get(sub_index, shift - num_bits)
    }
    Node(children, None) => {
      let branch_index = radix_indexing(index, shift)
      let sub_index = radix_subindex(index, shift)
      children[branch_index].get(sub_index, shift - num_bits)
    }
    Empty => abort("Index out of bounds")
  }
}

///|
fn[T] Tree::set(
  self : Tree[T],
  index : Int,
  shift : Int,
  value : T,
) -> Tree[T] where {
  proof_axiomatized: true,
  proof_require: tree_inv(self, root_level(shift)),
  proof_require: tree_valid_index_model(self, shift, index),
  proof_ensure: result => tree_set_post(self, shift, index, value, result),
} {
  match self {
    Leaf(leaf) => Leaf(immutable_set(leaf, index & bitmask, value))
    Node(children, Some(sizes)) => {
      let branch_index = get_branch_index(sizes, index)
      let sub_index = if branch_index == 0 {
        index
      } else {
        index - sizes[branch_index - 1]
      }
      Node(
        immutable_set(
          children,
          branch_index,
          children[branch_index].set(sub_index, shift - num_bits, value),
        ),
        Some(sizes),
      )
    }
    Node(children, None) => {
      let branch_index = radix_indexing(index, shift)
      let sub_index = index & ((1 << shift) - 1)
      Node(
        immutable_set(
          children,
          branch_index,
          children[branch_index].set(sub_index, shift - num_bits, value),
        ),
        None,
      )
    }
    Empty => abort("Index out of bounds")
  }
}

///|
fn append_sizes_last(
  sizes : ReadOnlyArray[Int]?,
  delta : Int,
) -> ReadOnlyArray[Int]? {
  match sizes {
    Some(values) =>
      Some(
        immutable_set(
          values,
          values.length() - 1,
          values[values.length() - 1] + delta,
        ),
      )
    None => None
  }
}

///|
fn push_sizes_last(
  sizes : ReadOnlyArray[Int]?,
  delta : Int,
) -> ReadOnlyArray[Int]? {
  match sizes {
    Some(values) =>
      Some(immutable_push(values, values[values.length() - 1] + delta))
    None => None
  }
}

///|
fn[T] Tree::append_right_leaf(
  self : Tree[T],
  shift : Int,
  leaf : ReadOnlyArray[T],
) -> (Tree[T], Int) where {
  proof_axiomatized: true,
  proof_require: tree_inv(self, root_level(shift)),
  proof_require: 0 < leaf.model().seq_length(),
  proof_require: leaf.model().seq_length() <= 32,
  proof_ensure: result => append_right_leaf_post(self, shift, leaf, result),
} {
  let delta = leaf.length()
  guard delta > 0 else { return (self, shift) }

  fn worker(
    node : Tree[T],
    shift : Int,
    leaf : ReadOnlyArray[T],
    delta : Int,
  ) -> Tree[T]? {
    match node {
      Leaf(elems) => {
        guard shift == 0 else { abort("Leaf should only appear at shift 0") }
        if elems.length() + delta <= branching_factor {
          Some(Leaf(immutable_concat(elems, leaf)))
        } else {
          None
        }
      }
      Node(nodes, sizes) => {
        let len = nodes.length()
        match worker(nodes[len - 1], shift - num_bits, leaf, delta) {
          Some(new_node) =>
            Some(
              Node(
                immutable_set(nodes, len - 1, new_node),
                append_sizes_last(sizes, delta),
              ),
            )
          None =>
            if len < branching_factor {
              Some(
                Node(
                  immutable_push(nodes, new_branch_left(leaf, shift - num_bits)),
                  push_sizes_last(sizes, delta),
                ),
              )
            } else {
              None
            }
        }
      }
      Empty => Some(Leaf(leaf))
    }
  }

  match worker(self, shift, leaf, delta) {
    Some(new_tree) => (new_tree, shift)
    None => {
      let new_branch = new_branch_left(leaf, shift)
      (
        match self {
          Leaf(_) => Node([self, new_branch], None)
          Node(_, Some(sizes)) => {
            let len = sizes[sizes.length() - 1]
            Node([self, new_branch], Some([len, len + delta]))
          }
          Node(_, None) => Node([self, new_branch], None)
          Empty => abort("Empty tree should have been handled in worker")
        },
        shift + num_bits,
      )
    }
  }
}
