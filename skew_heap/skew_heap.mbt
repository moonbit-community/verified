///|
/// A skew heap keeps the minimum at the root and leaves the children otherwise
/// unconstrained. The invariant only asks that every value below a node is at
/// least the node value, which is exactly what `merge` has to re-establish.
pub enum Heap {
  Empty
  Node(Int, Heap, Heap)
}

///|
#proof_pure
fn raw_node(value : Int, left : Heap, right : Heap) -> Heap {
  Node(value, left, right)
}

///|
fn heap_size(h : Heap) -> Int {
  match h {
    Empty => 0
    Node(_, left, right) => 1 + heap_size(left) + heap_size(right)
  }
}

///|
pub fn empty() -> Heap where { proof_ensure: result => heap_inv(result) } {
  Empty
}

///|
pub fn size(h : Heap) -> Int {
  heap_size(h)
}

///|
/// `make_node` is the proof bottleneck: both children must already be heaps,
/// and the chosen root must be no larger than either side. Once those
/// preconditions hold, the node constructor is enough to restore the
/// invariant after the recursive merge step.
fn make_node(
  value : Int,
  left : Heap,
  right : Heap,
) -> Heap where {
  proof_require: heap_inv(left),
  proof_require: heap_inv(right),
  proof_require: all_ge(value, left),
  proof_require: all_ge(value, right),
  proof_ensure: result => make_node_post(value, left, right, result),
} {
  let result = Node(value, left, right)
  proof_assert make_node_post(value, left, right, result)
  result
}

///|
/// The singleton heap is the base case for insertions and recursive merges.
/// Its proof is trivial because both children are empty and the root is
/// therefore the minimum by construction.
fn singleton(
  value : Int,
) -> Heap where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, Empty, Empty)
  proof_assert singleton_post(value, result)
  result
}

///|
/// `merge` is structurally recursive on total size. After comparing the two
/// roots, the recursive call always goes into one subtree of the chosen root,
/// so the termination argument is a size decrease and the correctness argument
/// is "recursive merge + `all_ge` + `make_node`".
pub fn merge(
  a : Heap,
  b : Heap,
) -> Heap where {
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
    (Node(va, la, ra), Node(vb, lb, rb)) =>
      if va <= vb {
        let merged = merge(ra, b)
        proof_assert all_ge(va, b)
        proof_assert all_ge(va, merged)
        let result = make_node(va, merged, la)
        proof_assert merge_post(a, b, result)
        result
      } else {
        let merged = merge(a, rb)
        proof_assert all_ge(vb, a)
        proof_assert all_ge(vb, merged)
        let result = make_node(vb, merged, lb)
        proof_assert merge_post(a, b, result)
        result
      }
  }
}

///|
/// Insertion is just `merge` with a one-element heap, so all of the ordering
/// and size proof obligations are delegated to the merge proof.
pub fn insert(
  h : Heap,
  value : Int,
) -> Heap where {
  proof_require: heap_inv(h),
  proof_ensure: result => insert_post(h, value, result),
} {
  let one = singleton(value)
  let result = merge(h, one)
  proof_assert insert_post(h, value, result)
  result
}

///|
/// A valid skew heap exposes its minimum at the root, so `find_min` only needs
/// to distinguish `Empty` from the non-empty case and then read the root
/// value.
pub fn find_min(
  h : Heap,
) -> Int? where {
  proof_require: heap_inv(h),
  proof_ensure: result => find_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, _, _) => {
      proof_assert root_minimum_post(h)
      Some(value)
    }
  }
}

///|
/// Deleting the minimum removes the root and merges the two subheaps. The
/// root-ordering invariant is what makes the children safe to merge directly.
pub fn delete_min(
  h : Heap,
) -> Heap? where {
  proof_require: heap_inv(h),
  proof_ensure: result => delete_min_post(h, result),
} {
  match h {
    Empty => None
    Node(value, left, right) => {
      let merged = merge(left, right)
      proof_assert all_ge(value, merged)
      Some(merged)
    }
  }
}

///|
/// Repeated insertion is the simplest way to build a valid heap from a list of
/// inputs; each step preserves the invariant via `insert`.
pub fn from_array(arr : ArrayView[Int]) -> Heap {
  arr.fold(init=Empty, (heap, value) => insert(heap, value))
}
