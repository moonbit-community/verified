///|
pub enum Heap {
  Empty
  Node(Int, Int, Heap, Heap)
} derive(Show)

///|
#proof_pure
fn rank(h : Heap) -> Int {
  match h {
    Empty => 0
    Node(_, rank, _, _) => rank
  }
}

///|
fn heap_size(h : Heap) -> Int {
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
fn raw_node(value : Int, stored_rank : Int, left : Heap, right : Heap) -> Heap {
  Node(value, stored_rank, left, right)
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
fn singleton(
  value : Int,
) -> Heap where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, 1, Empty, Empty)
  proof_assert singleton_post(value, result)
  result
}

///|
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
    (Node(va, _, la, ra), Node(vb, _, lb, rb)) =>
      if va <= vb {
        let merged = merge(ra, b)
        proof_assert merge_post(ra, b, merged)
        proof_assert all_ge(va, b)
        proof_assert all_ge(va, merged)
        let result = make_node(va, la, merged)
        proof_assert make_node_post(va, la, merged, result)
        proof_assert merge_post(a, b, result)
        result
      } else {
        let merged = merge(a, rb)
        proof_assert merge_post(a, rb, merged)
        proof_assert all_ge(vb, a)
        proof_assert all_ge(vb, merged)
        let result = make_node(vb, lb, merged)
        proof_assert make_node_post(vb, lb, merged, result)
        proof_assert merge_post(a, b, result)
        result
      }
  }
}

///|
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
pub fn find_min(
  h : Heap,
) -> Int? where {
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
pub fn delete_min(
  h : Heap,
) -> Heap? where {
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
