///|
/// A leftist heap stores a rank alongside each node, where the stored rank is
/// the null-path length of the right spine. The invariant combines the heap
/// ordering with the rank constraint that makes merges cheap.
pub enum Heap[T] {
  Empty
  Node(T, Int, Heap[T], Heap[T])
} derive(Debug)

///|
#proof_pure
fn[T] rank(h : Heap[T]) -> Int {
  match h {
    Empty => 0
    Node(_, rank, _, _) => rank
  }
}

///|
fn[T] heap_size(h : Heap[T]) -> Int {
  match h {
    Empty => 0
    Node(_, _, left, right) => 1 + heap_size(left) + heap_size(right)
  }
}

///|
#proof_pure
fn min2(a : Int, b : Int) -> Int {
  if a < b {
    a
  } else {
    b
  }
}

///|
#proof_pure
fn[T] raw_node(value : T, stored_rank : Int, left : Heap[T], right : Heap[T]) -> Heap[T] {
  Node(value, stored_rank, left, right)
}

///|
pub fn[T : Compare] empty() -> Heap[T] where { proof_ensure: result => heap_inv(result) } {
  Empty
}

///|
pub fn[T] size(h : Heap[T]) -> Int {
  heap_size(h)
}

///|
/// `make_node` is where the leftist property is restored. It chooses the child
/// arrangement so that the smaller-rank subtree stays on the right, then stores
/// `min(rank(left), rank(right)) + 1` as the node rank.
fn[T : Compare] make_node(
  value : T,
  left : Heap[T],
  right : Heap[T],
) -> Heap[T] where {
  proof_require: heap_inv(left),
  proof_require: heap_inv(right),
  proof_require: all_ge(value, left),
  proof_require: all_ge(value, right),
  proof_ensure: result => make_node_post(value, left, right, result),
} {
  if rank(left) < rank(right) {
    let result = Node(value, rank(left) + 1, right, left)
    proof_assert make_node_post(value, left, right, result)
    result
  } else {
    let result = Node(value, rank(right) + 1, left, right)
    proof_assert make_node_post(value, left, right, result)
    result
  }
}

///|
/// A singleton heap has rank 1 and empty children, so it satisfies the
/// invariant without any balancing work.
fn[T : Compare] singleton(
  value : T,
) -> Heap[T] where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, 1, Empty, Empty)
  proof_assert singleton_post(value, result)
  result
}

///|
/// Merge mirrors the skew-heap proof but adds the rank side condition. The
/// recursive call always follows the right subtree of the chosen root, which is
/// what keeps the measure decreasing and lets `make_node` rebuild the leftist
/// shape afterward.
pub fn[T : Compare] merge(
  a : Heap[T],
  b : Heap[T],
) -> Heap[T] where {
  proof_decrease: merge_measure(a, b),
  proof_require: heap_inv(a),
  proof_require: heap_inv(b),
  proof_ensure: result => merge_post(a, b, result),
} {
  match (a, b) {
    (Empty, _) => {
      proof_assert merge_post(a, b, b)
      b
    }
    (_, Empty) => {
      proof_assert merge_post(a, b, a)
      a
    }
    (Node(va, ra_rank, la, ra), Node(vb, rb_rank, lb, rb)) =>
      if va <= vb {
        let merged = merge(ra, b)
        proof_assert merge_post(ra, b, merged)
        proof_assert all_ge(va, b)
        proof_assert all_ge(va, merged)
        let result = make_node(va, la, merged)
        proof_assert make_node_post(va, la, merged, result)
        proof_assert merge_post(raw_node(va, ra_rank, la, ra), b, result)
        proof_assert merge_post(a, b, result)
        result
      } else {
        let merged = merge(a, rb)
        proof_assert merge_post(a, rb, merged)
        proof_assert all_ge(vb, a)
        proof_assert all_ge(vb, merged)
        let result = make_node(vb, lb, merged)
        proof_assert make_node_post(vb, lb, merged, result)
        proof_assert merge_post(a, raw_node(vb, rb_rank, lb, rb), result)
        proof_assert merge_post(a, b, result)
        result
      }
  }
}

///|
/// Insertion is still just merge with a singleton, so the heap-order and rank
/// proof obligations are inherited from the merge step.
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
/// The minimum is always stored at the root, so `find_min` only reads that
/// value after the invariant rules out the empty case.
pub fn[T : Compare] find_min(
  h : Heap[T],
) -> T? where {
  proof_require: heap_inv(h),
  proof_ensure: result => find_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, _, _, _) => {
      proof_assert root_minimum_post(h)
      Some(value)
    }
  }
}

///|
/// Deleting the minimum discards the root and merges the two children. The
/// rank invariant is preserved because the merge result is rewrapped through
/// `make_node` inside the recursive merge proof.
pub fn[T : Compare] delete_min(
  h : Heap[T],
) -> Heap[T]? where {
  proof_require: heap_inv(h),
  proof_ensure: result => delete_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, _, left, right) => {
      let merged = merge(left, right)
      proof_assert all_ge(value, merged)
      Some(merged)
    }
  }
}
