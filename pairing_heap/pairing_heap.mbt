///|
/// A pairing heap stores a root value, a list of child heaps, and the cached
/// size. The child list invariant is the important part: every child must be a
/// valid non-empty heap, so the root of each child can participate in later
/// pairwise merges.
pub enum Heap[T] {
  Empty
  Node(T, ChildList[T], Int)
} derive(Debug)

///|
/// The child list is just the forest hanging off the root, but its invariant
/// is stronger than a plain list: each entry must itself be a non-empty heap.
pub enum ChildList[T] {
  Nil
  Cons(Heap[T], ChildList[T])
} derive(Debug)

///|
/// The empty heap is valid immediately; the invariant has nothing to check in
/// the `Empty` case.
pub fn[T : Compare] empty() -> Heap[T] where { proof_ensure: result => heap_inv(result) } {
  Empty
}

///|
/// `size` is the cached count stored in the root, so no traversal is needed to
/// answer it once the invariant has been established.
pub fn[T] size(h : Heap[T]) -> Int {
  match h {
    Empty => 0
    Node(_, _, n) => n
  }
}

///|
/// A singleton heap is the atomic proof case: one root, no children, and size
/// exactly one.
fn[T : Compare] singleton(
  value : T,
) -> Heap[T] where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, Nil, 1)
  result
}

///|
/// Merge keeps the smaller root and attaches the other heap as a new child.
/// That is why the size equation is exact and the child-list invariant stays
/// local: the losing heap is already valid and non-empty.
pub fn[T : Compare] merge(
  a : Heap[T],
  b : Heap[T],
) -> Heap[T] where {
  proof_require: heap_inv(a),
  proof_require: heap_inv(b),
  proof_ensure: result => merge_post(a, b, result),
} {
  match (a, b) {
    (Empty, _) => b
    (_, Empty) => a
    (Node(va, children_a, size_a), Node(vb, children_b, size_b)) =>
      if va <= vb {
        let result = Node(va, Cons(b, children_a), size_a + size_b)
        proof_assert merge_post(a, b, result)
        result
      } else {
        let result = Node(vb, Cons(a, children_b), size_a + size_b)
        proof_assert merge_post(a, b, result)
        result
      }
  }
}

///|
/// `merge_pairs_list` is the recursive pairing phase from delete-min. The
/// decrease metric is the number of children, and the two-child case shrinks it
/// by merging a pair first and then folding the rest back in.
fn[T : Compare] merge_pairs_list(
  xs : ChildList[T],
) -> Heap[T] where {
  proof_decrease: list_length_model(xs),
  proof_require: list_inv(xs),
  proof_ensure: result => merge_pairs_post(xs, result),
} {
  match xs {
    Nil => {
      proof_assert merge_pairs_post(xs, Empty)
      Empty
    }
    Cons(h, Nil) => {
      proof_assert merge_pairs_post(xs, h)
      h
    }
    Cons(h1, Cons(h2, rest)) => {
      proof_assert 0 <= list_length_model(xs)
      proof_assert non_empty(h1)
      proof_assert non_empty(h2)
      proof_assert list_length_model(rest) < list_length_model(xs)
      let first = merge(h1, h2)
      let rest_merged = merge_pairs_list(rest)
      let result = merge(first, rest_merged)
      proof_assert merge_pairs_post(xs, result)
      result
    }
  }
}

///|
/// Insertion is just merge with a singleton heap, so the proof reduces to the
/// merge proof plus the singleton base case.
pub fn[T : Compare] insert(
  h : Heap[T],
  value : T,
) -> Heap[T] where {
  proof_require: heap_inv(h),
  proof_ensure: result => insert_post(h, value, result),
} {
  let one = singleton(value)
  let result = merge(h, one)
  proof_assert insert_post(h, value, result)
  result
}

///|
/// The minimum is the root value when the heap is non-empty. The proof first
/// rules out the empty case via the root-count fact, then returns that cached
/// root.
pub fn[T : Compare] find_min(
  h : Heap[T],
) -> T? where {
  proof_require: heap_inv(h),
  proof_ensure: result => find_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, _, _) => {
      proof_assert root_count_positive_post(h)
      let result = Some(value)
      proof_assert find_min_post(h, result)
      result
    }
  }
}

///|
/// Deleting the minimum removes the root and then pairwise-merges the children.
/// The child-list invariant is exactly what lets the merged forest remain a
/// valid heap.
pub fn[T : Compare] delete_min(
  h : Heap[T],
) -> Heap[T]? where {
  proof_require: heap_inv(h),
  proof_ensure: result => delete_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, children, _) => {
      let merged = merge_pairs_list(children)
      proof_assert all_ge(value, merged)
      let result = Some(merged)
      proof_assert delete_min_post(h, result)
      result
    }
  }
}
