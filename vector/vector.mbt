///|
fn[T] Vector::tail_offset(
  self : Vector[T],
) -> Int where {
  proof_ensure: result => tail_offset_post(self, result),
} {
  self.size - self.tail.length()
}

///|
#as_free_fn
pub fn[T] Vector::new() -> Vector[T] where {
  proof_ensure: result => new_post(result),
} {
  { tree: Tree::empty(), tail: [], size: 0, shift: 0 }
}

///|
pub fn[T] Vector::length(
  self : Vector[T],
) -> Int where {
  proof_require: vector_inv(self),
  proof_ensure: result => length_post(self, result),
} {
  self.size
}

///|
pub fn[T] Vector::is_empty(
  self : Vector[T],
) -> Bool where {
  proof_require: vector_inv(self),
  proof_ensure: result => is_empty_post(self, result),
} {
  self.size == 0
}

///|
#alias("_[_]")
pub fn[T : Eq] Vector::at(
  self : Vector[T],
  index : Int,
) -> T where {
  proof_require: vector_inv(self),
  proof_require: valid_index_model(self, index),
  proof_ensure: result => at_post(self, index, result),
} {
  if !(index >= 0 && index < self.size) {
    panic()
  }
  if index >= self.tail_offset() {
    self.tail[index - self.tail_offset()]
  } else {
    self.tree.get(index, self.shift)
  }
}

///|
pub fn[T : Eq] Vector::get(
  self : Vector[T],
  index : Int,
) -> T? where {
  proof_require: vector_inv(self),
  proof_ensure: result => get_post_model(self, index, result),
} {
  if 0 <= index && index < self.size {
    Some(self[index])
  } else {
    None
  }
}

///|
pub fn[T : Eq] Vector::peek(
  self : Vector[T],
) -> T? where {
  proof_require: vector_inv(self),
  proof_ensure: result => peek_post_model(self, result),
} {
  if self.size == 0 {
    None
  } else {
    Some(self[self.size - 1])
  }
}

///|
pub fn[T] Vector::set(
  self : Vector[T],
  index : Int,
  value : T,
) -> Vector[T] where {
  proof_require: vector_inv(self),
  proof_require: valid_index_model(self, index),
  proof_ensure: result => set_post_model(self, index, value, result),
} {
  if !(index >= 0 && index < self.size) {
    panic()
  }
  let tail_len = self.tail.length()
  if tail_len == 0 {
    {
      tree: self.tree.set(index, self.shift, value),
      tail: self.tail,
      size: self.size,
      shift: self.shift,
    }
  } else {
    let tail_offset = self.tail_offset()
    if index >= tail_offset {
      {
        tree: self.tree,
        tail: immutable_set(self.tail, index - tail_offset, value),
        size: self.size,
        shift: self.shift,
      }
    } else {
      {
        tree: self.tree.set(index, self.shift, value),
        tail: self.tail,
        size: self.size,
        shift: self.shift,
      }
    }
  }
}

///|
pub fn[T] Vector::push(
  self : Vector[T],
  value : T,
) -> Vector[T] where {
  proof_require: vector_inv(self),
  proof_ensure: result => push_post_model(self, value, result),
} {
  if self.tail.length() < 32 {
    {
      tree: self.tree,
      tail: immutable_push(self.tail, value),
      size: self.size + 1,
      shift: self.shift,
    }
  } else {
    match self.tree {
      Empty =>
        {
          tree: Leaf(self.tail),
          tail: immutable_push([], value),
          size: self.size + 1,
          shift: 0,
        }
      _ => {
        let (tree, shift) = self.tree.append_right_leaf(self.shift, self.tail)
        { tree, tail: immutable_push([], value), size: self.size + 1, shift }
      }
    }
  }
}

///|
fn[T] Vector::pop_singleton_tail(
  self : Vector[T],
) -> Vector[T] where {
  proof_axiomatized: true,
  proof_require: vector_inv(self),
  proof_require: self.tail.length() == 1,
  proof_require: 1 < self.size,
  proof_ensure: result => pop_singleton_tail_post(self, result),
} {
  let new_tail = self.tree.last_leaf_elements()
  let (tree, shift) = self.tree
    .pop_rightmost_leaf(self.shift)
    .shrink_top(self.shift)
  { tree, tail: new_tail, size: self.size - 1, shift }
}

///|
fn[T] Vector::pop_tree_only(
  self : Vector[T],
) -> Vector[T] where {
  proof_axiomatized: true,
  proof_require: vector_inv(self),
  proof_require: self.tail.length() == 0,
  proof_require: 1 < self.size,
  proof_ensure: result => pop_tree_only_post(self, result),
} {
  let last_leaf = self.tree.last_leaf_elements()
  if last_leaf.length() > 1 {
    let (tree, shift) = self.tree
      .pop_rightmost_leaf(self.shift)
      .shrink_top(self.shift)
    {
      tree,
      tail: immutable_slice(last_leaf, 0, last_leaf.length() - 1),
      size: self.size - 1,
      shift,
    }
  } else {
    let stripped = self.tree.pop_rightmost_leaf(self.shift)
    let (promoted_tree, promoted_shift) = stripped.shrink_top(self.shift)
    if promoted_tree is Empty {
      new()
    } else {
      let new_tail = promoted_tree.last_leaf_elements()
      let (tree, shift) = promoted_tree
        .pop_rightmost_leaf(promoted_shift)
        .shrink_top(promoted_shift)
      { tree, tail: new_tail, size: self.size - 1, shift }
    }
  }
}

///|
pub fn[T] Vector::pop(
  self : Vector[T],
) -> Vector[T]? where {
  proof_require: vector_inv(self),
  proof_ensure: result => pop_post_model(self, result),
} {
  if self.size == 0 {
    None
  } else if self.size == 1 {
    Some(new())
  } else if self.tail.length() > 1 {
    Some({
      tree: self.tree,
      tail: immutable_slice(self.tail, 0, self.tail.length() - 1),
      size: self.size - 1,
      shift: self.shift,
    })
  } else if self.tail.length() == 1 {
    Some(self.pop_singleton_tail())
  } else {
    Some(self.pop_tree_only())
  }
}
