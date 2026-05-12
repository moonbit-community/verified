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
  let result = { tree: Tree::empty(), tail: [], size: 0, shift: 0 }
  proof_assert result.size == 0
  proof_assert result.shift == 0
  proof_assert result.tail.length() == 0
  proof_assert 0 <= result.shift
  proof_assert result.size - result.tail.length() == 0
  proof_assert @mathint.int_model(result.size) == @mathint.int_model(0)
  proof_assert @mathint.int_model(result.size - result.tail.length()) ==
    @mathint.int_model(0)
  proof_assert vector_tree_inv(result.tree, root_level(result.shift))
  proof_assert vector_tree_model(result.tree, root_level(result.shift)).length() ==
    @mathint.int_model(0)
  proof_assert @readonlyarray.model(result.tail).length() ==
    @mathint.int_model(0)
  proof_assert result.model().length() == @mathint.int_model(0)
  proof_assert vector_inv(result)
  proof_assert new_post(result)
  result
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
  let tail_offset = self.tail_offset()
  if index >= tail_offset {
    let result = self.tail[index - tail_offset]
    proof_assert tail_offset_post(self, tail_offset)
    proof_assert result == self.model().get(@mathint.int_model(index))
    proof_assert at_post(self, index, result)
    result
  } else {
    match self.tree {
      Empty => panic()
      _ => {
        proof_assert tree_inv(self.tree, root_level(self.shift))
        proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
          tree_model(self.tree, root_level(self.shift))
        proof_assert tree_valid_index_model(self.tree, self.shift, index)
        let result = self.tree.get(index, self.shift)
        proof_assert tree_get_post(self.tree, self.shift, index, result)
        proof_assert result == self.model().get(@mathint.int_model(index))
        proof_assert at_post(self, index, result)
        result
      }
    }
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
    match self.tree {
      Empty => panic()
      _ => {
        proof_assert tree_inv(self.tree, root_level(self.shift))
        proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
          tree_model(self.tree, root_level(self.shift))
        proof_assert tree_valid_index_model(self.tree, self.shift, index)
        let new_tree = self.tree.set(index, self.shift, value)
        proof_assert tree_set_post(
          self.tree,
          self.shift,
          index,
          value,
          new_tree,
        )
        let result = {
          tree: new_tree,
          tail: self.tail,
          size: self.size,
          shift: self.shift,
        }
        proof_assert vector_inv(result)
        proof_assert set_post_model(self, index, value, result)
        result
      }
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
      match self.tree {
        Empty => panic()
        _ => {
          proof_assert tree_inv(self.tree, root_level(self.shift))
          proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
            tree_model(self.tree, root_level(self.shift))
          proof_assert tree_valid_index_model(self.tree, self.shift, index)
          let new_tree = self.tree.set(index, self.shift, value)
          proof_assert tree_set_post(
            self.tree,
            self.shift,
            index,
            value,
            new_tree,
          )
          let result = {
            tree: new_tree,
            tail: self.tail,
            size: self.size,
            shift: self.shift,
          }
          proof_assert vector_inv(result)
          proof_assert set_post_model(self, index, value, result)
          result
        }
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
    let new_tail = immutable_push(self.tail, value)
    proof_assert immutable_push_post(self.tail, value, new_tail)
    let result = {
      tree: self.tree,
      tail: new_tail,
      size: self.size + 1,
      shift: self.shift,
    }
    proof_assert result.model() == self.model().append(Seq::singleton(value))
    proof_assert vector_inv(result)
    proof_assert push_post_model(self, value, result)
    result
  } else {
    match self.tree {
      Empty => {
        let empty_tail : ReadOnlyArray[T] = []
        let new_tail = immutable_push(empty_tail, value)
        proof_assert immutable_push_post(empty_tail, value, new_tail)
        proof_assert @readonlyarray.model(self.tail).length() <=
          @mathint.int_model(32)
        proof_assert @mathint.int_model(32) <=
          @readonlyarray.model(self.tail).length()
        proof_assert @readonlyarray.model(self.tail).length() ==
          @mathint.int_model(32)
        proof_assert @mathint.int_model(0) <
          @readonlyarray.model(self.tail).length()
        let new_tree = Tree::from_leaf(self.tail)
        proof_assert leaf_tree_post(self.tail, new_tree)
        proof_assert root_level(0) == 0
        proof_assert tree_inv(new_tree, 0)
        proof_assert tree_inv(new_tree, root_level(0))
        let result = {
          tree: new_tree,
          tail: new_tail,
          size: self.size + 1,
          shift: 0,
        }
        proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
          Seq::empty()
        proof_assert self.model() == @readonlyarray.model(self.tail)
        proof_assert @readonlyarray.model(empty_tail) == Seq::empty()
        proof_assert @readonlyarray.model(new_tail) == Seq::singleton(value)
        proof_assert vector_tree_model(new_tree, root_level(0)) ==
          @readonlyarray.model(self.tail)
        proof_assert result.model() ==
          @readonlyarray.model(self.tail).append(Seq::singleton(value))
        proof_assert result.model() ==
          self.model().append(Seq::singleton(value))
        proof_assert vector_inv(result)
        proof_assert push_post_model(self, value, result)
        result
      }
      _ => {
        let (tree, shift) = self.tree.append_right_leaf(self.shift, self.tail)
        proof_assert append_right_leaf_post(
          self.tree,
          self.shift,
          self.tail,
          (tree, shift),
        )
        let empty_tail : ReadOnlyArray[T] = []
        let new_tail = immutable_push(empty_tail, value)
        proof_assert immutable_push_post(empty_tail, value, new_tail)
        proof_assert 0 <= shift
        proof_assert @readonlyarray.model(empty_tail) == Seq::empty()
        proof_assert @readonlyarray.model(new_tail) == Seq::singleton(value)
        let result = { tree, tail: new_tail, size: self.size + 1, shift }
        proof_assert result.model() ==
          self.model().append(Seq::singleton(value))
        proof_assert vector_inv(result)
        proof_assert push_post_model(self, value, result)
        result
      }
    }
  }
}

///|
fn[T] Vector::pop_singleton_tail(
  self : Vector[T],
) -> Vector[T] where {
  proof_require: vector_inv(self),
  proof_require: self.tail.length() == 1,
  proof_require: 1 < self.size,
  proof_ensure: result => pop_singleton_tail_post(self, result),
} {
  proof_assert @readonlyarray.model(self.tail).length() == @mathint.int_model(1)
  proof_assert @mathint.int_model(1) < @mathint.int_model(self.size)
  proof_assert vector_tree_model(self.tree, root_level(self.shift)).length() ==
    @mathint.int_model(self.size - self.tail.length())
  proof_assert !empty_tree_post(self.tree)
  proof_assert tree_inv(self.tree, root_level(self.shift))
  proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
    tree_model(self.tree, root_level(self.shift))
  proof_assert tree_model(self.tree, root_level(self.shift)).length() ==
    vector_tree_model(self.tree, root_level(self.shift)).length()
  proof_assert @mathint.int_model(0) <
    tree_model(self.tree, root_level(self.shift)).length()
  let new_tail = self.tree.last_leaf_elements(self.shift)
  proof_assert last_leaf_elements_post(self.tree, self.shift, new_tail)
  let stripped = self.tree.pop_rightmost_leaf(self.shift)
  proof_assert pop_rightmost_leaf_post(self.tree, self.shift, stripped)
  let (tree, shift) = stripped.shrink_top(self.shift)
  let result = { tree, tail: new_tail, size: self.size - 1, shift }
  proof_assert shrink_top_post(stripped, self.shift, (tree, shift))
  proof_assert result.model() == tree_model(self.tree, root_level(self.shift))
  proof_assert result.model() ==
    self
    .model()
    .sub(@mathint.int_model(0), self.model().length() - @mathint.int_model(1))
  proof_assert vector_inv(result)
  proof_assert pop_singleton_tail_post(self, result)
  result
}

///|
fn[T] Vector::pop_tree_only(
  self : Vector[T],
) -> Vector[T] where {
  proof_require: vector_inv(self),
  proof_require: self.tail.length() == 0,
  proof_require: 1 < self.size,
  proof_ensure: result => pop_tree_only_post(self, result),
} {
  proof_assert @readonlyarray.model(self.tail).length() == @mathint.int_model(0)
  proof_assert @mathint.int_model(1) < @mathint.int_model(self.size)
  proof_assert vector_tree_model(self.tree, root_level(self.shift)).length() ==
    @mathint.int_model(self.size - self.tail.length())
  match self.tree {
    Empty => panic()
    _ => {
      proof_assert tree_inv(self.tree, root_level(self.shift))
      proof_assert vector_tree_model(self.tree, root_level(self.shift)) ==
        tree_model(self.tree, root_level(self.shift))
      proof_assert tree_model(self.tree, root_level(self.shift)).length() ==
        vector_tree_model(self.tree, root_level(self.shift)).length()
      proof_assert @mathint.int_model(0) <
        tree_model(self.tree, root_level(self.shift)).length()
      let last_leaf = self.tree.last_leaf_elements(self.shift)
      proof_assert last_leaf_elements_post(self.tree, self.shift, last_leaf)
      if last_leaf.length() > 1 {
        let stripped = self.tree.pop_rightmost_leaf(self.shift)
        proof_assert pop_rightmost_leaf_post(self.tree, self.shift, stripped)
        let (tree, shift) = stripped.shrink_top(self.shift)
        proof_assert shrink_top_post(stripped, self.shift, (tree, shift))
        let result = {
          tree,
          tail: immutable_slice(last_leaf, 0, last_leaf.length() - 1),
          size: self.size - 1,
          shift,
        }
        proof_assert vector_inv(result)
        proof_assert pop_tree_only_post(self, result)
        result
      } else {
        let stripped = self.tree.pop_rightmost_leaf(self.shift)
        proof_assert pop_rightmost_leaf_post(self.tree, self.shift, stripped)
        let (promoted_tree, promoted_shift) = stripped.shrink_top(self.shift)
        proof_assert shrink_top_post(
          stripped,
          self.shift,
          (promoted_tree, promoted_shift),
        )
        match promoted_tree {
          Empty => new()
          _ => {
            proof_assert !empty_tree_post(promoted_tree)
            proof_assert tree_inv(promoted_tree, root_level(promoted_shift))
            proof_assert vector_tree_model(
                promoted_tree,
                root_level(promoted_shift),
              ) ==
              tree_model(promoted_tree, root_level(promoted_shift))
            proof_assert @mathint.int_model(0) <
              tree_model(promoted_tree, root_level(promoted_shift)).length()
            let new_tail = promoted_tree.last_leaf_elements(promoted_shift)
            proof_assert last_leaf_elements_post(
              promoted_tree, promoted_shift, new_tail,
            )
            let stripped = promoted_tree.pop_rightmost_leaf(promoted_shift)
            proof_assert pop_rightmost_leaf_post(
              promoted_tree, promoted_shift, stripped,
            )
            let (tree, shift) = stripped.shrink_top(promoted_shift)
            proof_assert shrink_top_post(
              stripped,
              promoted_shift,
              (tree, shift),
            )
            let result = { tree, tail: new_tail, size: self.size - 1, shift }
            proof_assert vector_inv(result)
            proof_assert pop_tree_only_post(self, result)
            result
          }
        }
      }
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
    proof_assert self.model().length() == @mathint.int_model(0)
    proof_assert pop_post_model(self, None)
    None
  } else if self.size == 1 {
    let result = new()
    proof_assert new_post(result)
    proof_assert @mathint.int_model(0) < self.model().length()
    proof_assert result.model() ==
      self
      .model()
      .sub(@mathint.int_model(0), self.model().length() - @mathint.int_model(1))
    proof_assert pop_post_model(self, Some(result))
    Some(result)
  } else if self.tail.length() > 1 {
    let new_tail = immutable_slice(self.tail, 0, self.tail.length() - 1)
    proof_assert immutable_slice_post(
      self.tail,
      0,
      self.tail.length() - 1,
      new_tail,
    )
    let result = {
      tree: self.tree,
      tail: new_tail,
      size: self.size - 1,
      shift: self.shift,
    }
    proof_assert vector_inv(result)
    proof_assert result.model() ==
      self
      .model()
      .sub(@mathint.int_model(0), self.model().length() - @mathint.int_model(1))
    proof_assert pop_post_model(self, Some(result))
    Some(result)
  } else if self.tail.length() == 1 {
    let result = self.pop_singleton_tail()
    proof_assert pop_singleton_tail_post(self, result)
    proof_assert pop_post_model(self, Some(result))
    Some(result)
  } else {
    let result = self.pop_tree_only()
    proof_assert pop_tree_only_post(self, result)
    proof_assert pop_post_model(self, Some(result))
    Some(result)
  }
}
