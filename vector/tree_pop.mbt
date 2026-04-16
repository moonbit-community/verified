///|
fn[T] Tree::last_leaf_elements(self : Tree[T]) -> ReadOnlyArray[T] {
  match self {
    Leaf(leaf) => leaf
    Node(children, _) => children[children.length() - 1].last_leaf_elements()
    Empty => abort("Empty tree has no last leaf")
  }
}

///|
fn[T] Tree::pop_rightmost_leaf(self : Tree[T], shift : Int) -> Tree[T] {
  match self {
    Empty => Empty
    Leaf(_) => Empty
    Node(children, _) => {
      let last_index = children.length() - 1
      let new_last = children[last_index].pop_rightmost_leaf(shift - num_bits)
      if new_last is Empty {
        if last_index == 0 {
          Empty
        } else {
          let new_children = immutable_slice(children, 0, last_index)
          Node(new_children, compute_sizes(new_children, shift - num_bits))
        }
      } else {
        let new_children = immutable_set(children, last_index, new_last)
        Node(new_children, compute_sizes(new_children, shift - num_bits))
      }
    }
  }
}

///|
fn[T] Tree::shrink_top(self : Tree[T], shift : Int) -> (Tree[T], Int) {
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
