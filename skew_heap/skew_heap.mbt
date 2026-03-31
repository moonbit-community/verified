///|
pub enum Heap {
  Empty
  Node(Int, Heap, Heap)
} derive(Show)

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
pub fn empty() -> Heap where {
  proof_ensure: result => heap_inv(result),
} {
  Empty
}

///|
pub fn size(h : Heap) -> Int {
  heap_size(h)
}

///|
fn make_node(value : Int, left : Heap, right : Heap) -> Heap where {
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
fn singleton(value : Int) -> Heap where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, Empty, Empty)
  proof_assert singleton_post(value, result)
  result
}

///|
pub fn merge(a : Heap, b : Heap) -> Heap where {
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
pub fn insert(h : Heap, value : Int) -> Heap where {
  proof_require: heap_inv(h),
  proof_ensure: result => insert_post(h, value, result),
} {
  let one = singleton(value)
  let result = merge(h, one)
  proof_assert insert_post(h, value, result)
  result
}

///|
pub fn find_min(h : Heap) -> Int? where {
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
pub fn delete_min(h : Heap) -> Heap? where {
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
pub fn from_array(arr : ArrayView[Int]) -> Heap {
  arr.fold(init=Empty, (heap, value) => insert(heap, value))
}
