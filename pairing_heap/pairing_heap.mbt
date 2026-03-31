///|
pub enum Heap {
  Empty
  Node(Int, ChildList, Int)
} derive(Show)

///|
pub enum ChildList {
  Nil
  Cons(Heap, ChildList)
} derive(Show)

///|
#proof_pure
fn raw_node(value : Int, children : ChildList, size : Int) -> Heap {
  Node(value, children, size)
}

///|
#proof_pure
fn raw_cons(head : Heap, tail : ChildList) -> ChildList {
  Cons(head, tail)
}

pub fn empty() -> Heap where { proof_ensure: result => heap_inv(result) } {
  Empty
}

///|
pub fn size(h : Heap) -> Int {
  match h {
    Empty => 0
    Node(_, _, n) => n
  }
}

///|
fn singleton(value : Int) -> Heap where {
  proof_ensure: result => singleton_post(value, result),
} {
  let result = Node(value, Nil, 1)
  proof_assert singleton_post(value, result)
  result
}

///|
pub fn merge(a : Heap, b : Heap) -> Heap where {
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
fn merge_pairs_list(xs : ChildList) -> Heap where {
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
      proof_assert root_count_positive_post(h)
      let result = Some(value)
      proof_assert find_min_post(h, result)
      result
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
    Node(value, children, _) => {
      let merged = merge_pairs_list(children)
      proof_assert all_ge(value, merged)
      let result = Some(merged)
      proof_assert delete_min_post(h, result)
      result
    }
  }
}
