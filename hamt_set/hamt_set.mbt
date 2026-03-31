///|
using @bitmap32 {bitmap_add, bitmap_remove, uint_bit0, uint_lsr, zero_uint}

///|
priv enum Bucket {
  Empty
  More(Int, Bucket)
} derive(Eq)

///|
enum Node {
  Flat(Int)
  Leaf(Int, Bucket)
  Branch(Children)
} derive(Eq)

///|
priv struct Children {
  bitmap : UInt
  data : FixedArray[Node]
} derive(Eq)

///|
pub struct HashSet {
  root : Node?
} derive(Eq)

///|
const MAX_SLOT_LEVEL : Int = 7

///|
fn hash_nat(key : Int) -> Int {
  if key >= 0 {
    key / 2
  } else {
    (-1 - key) / 2
  }
}

///|
fn pow32(level : Int) -> Int {
  for i = 0, acc = 1; i < level; {
    continue i + 1, acc * 32
  } nobreak {
    acc
  }
}

///|
fn slot(key : Int, level : Int) -> Int {
  hash_nat(key) / pow32(level) % 32
}

///|
fn bucket_contains(bucket : Bucket, key : Int) -> Bool {
  match bucket {
    Empty => false
    More(head, tail) => head == key || bucket_contains(tail, key)
  }
}

///|
fn bucket_add(bucket : Bucket, key : Int) -> Bucket {
  if bucket_contains(bucket, key) {
    bucket
  } else {
    More(key, bucket)
  }
}

///|
fn bucket_remove(bucket : Bucket, key : Int) -> (Bool, Bucket) {
  match bucket {
    Empty => (false, Empty)
    More(head, tail) =>
      if head == key {
        (true, tail)
      } else {
        let (removed, rest) = bucket_remove(tail, key)
        (removed, More(head, rest))
      }
  }
}

///|
fn bucket_length(bucket : Bucket) -> Int {
  match bucket {
    Empty => 0
    More(_, tail) => 1 + bucket_length(tail)
  }
}

///|
fn children_mem(bitmap : UInt, idx : Int) -> Bool {
  let shifted = uint_lsr(bitmap, idx)
  uint_bit0(shifted)
}

///|
fn children_rank(bitmap : UInt, idx : Int) -> Int {
  for j = 0, acc = 0; j < idx; {
    continue j + 1, if children_mem(bitmap, j) { acc + 1 } else { acc }
  } nobreak {
    acc
  }
}

///|
fn children_empty() -> Children {
  { bitmap: zero_uint(), data: FixedArray::make(0, Flat(0)) }
}

///|
fn children_singleton(idx : Int, child : Node) -> Children {
  { bitmap: bitmap_add(zero_uint(), idx), data: FixedArray::make(1, child) }
}

///|
fn children_doubleton(
  idx1 : Int,
  child1 : Node,
  idx2 : Int,
  child2 : Node,
) -> Children {
  {
    bitmap: if idx1 < idx2 {
      bitmap_add(bitmap_add(zero_uint(), idx1), idx2)
    } else {
      bitmap_add(bitmap_add(zero_uint(), idx2), idx1)
    },
    data: if idx1 < idx2 {
      [child1, child2]
    } else {
      [child2, child1]
    },
  }
}

///|
fn children_get(children : Children, idx : Int) -> Node? {
  if children_mem(children.bitmap, idx) {
    Some(children.data[children_rank(children.bitmap, idx)])
  } else {
    None
  }
}

///|
fn children_add(children : Children, idx : Int, child : Node) -> Children {
  let old_data = children.data
  let old_len = old_data.length()
  let pos = children_rank(children.bitmap, idx)
  let new_data = FixedArray::make(old_len + 1, child)
  for i = 0; i < pos; {
    new_data[i] = old_data[i]
    continue i + 1
  }
  new_data[pos] = child
  for i = pos; i < old_len; {
    new_data[i + 1] = old_data[i]
    continue i + 1
  }
  { bitmap: bitmap_add(children.bitmap, idx), data: new_data }
}

///|
fn children_replace(children : Children, idx : Int, child : Node) -> Children {
  let new_data = children.data.copy()
  new_data[children_rank(children.bitmap, idx)] = child
  { bitmap: children.bitmap, data: new_data }
}

///|
fn children_remove(children : Children, idx : Int) -> Children {
  let old_data = children.data
  let old_len = old_data.length()
  if old_len == 1 {
    children_empty()
  } else {
    let pos = children_rank(children.bitmap, idx)
    let new_data = FixedArray::make(old_len - 1, old_data[0])
    for i = 0; i < pos; {
      new_data[i] = old_data[i]
      continue i + 1
    }
    for i = pos; i < old_len - 1; {
      new_data[i] = old_data[i + 1]
      continue i + 1
    }
    { bitmap: bitmap_remove(children.bitmap, idx), data: new_data }
  }
}

///|
fn children_length(children : Children) -> Int {
  children.data.length()
}

///|
fn join_2(key1 : Int, key2 : Int, level : Int) -> Node {
  let idx1 = slot(key1, level)
  let idx2 = slot(key2, level)
  if idx1 == idx2 {
    let child = if level == MAX_SLOT_LEVEL - 1 {
      Leaf(key2, More(key1, Empty))
    } else {
      join_2(key1, key2, level + 1)
    }
    Branch(children_singleton(idx1, child))
  } else {
    let child1 = if level == MAX_SLOT_LEVEL - 1 {
      Leaf(key1, Empty)
    } else {
      Flat(key1)
    }
    let child2 = if level == MAX_SLOT_LEVEL - 1 {
      Leaf(key2, Empty)
    } else {
      Flat(key2)
    }
    Branch(children_doubleton(idx1, child1, idx2, child2))
  }
}

///|
fn contains_at(node : Node, key : Int, level : Int) -> Bool {
  match node {
    Flat(key1) => key == key1
    Leaf(head, bucket) => key == head || bucket_contains(bucket, key)
    Branch(children) => {
      let idx = slot(key, level)
      match children_get(children, idx) {
        None => false
        Some(child) => contains_at(child, key, level + 1)
      }
    }
  }
}

///|
fn add_at(node : Node, key : Int, level : Int) -> Node {
  match node {
    Flat(key1) => if key == key1 { node } else { join_2(key1, key, level) }
    Leaf(head, bucket) =>
      if key == head || bucket_contains(bucket, key) {
        node
      } else {
        Leaf(head, bucket_add(bucket, key))
      }
    Branch(children) => {
      let idx = slot(key, level)
      match children_get(children, idx) {
        None => Branch(children_add(children, idx, Flat(key)))
        Some(child) =>
          Branch(children_replace(children, idx, add_at(child, key, level + 1)))
      }
    }
  }
}

///|
fn collapse_branch(children : Children) -> Node {
  if children_length(children) == 1 {
    let only = children.data[0]
    match only {
      Flat(key) => Flat(key)
      _ => Branch(children)
    }
  } else {
    Branch(children)
  }
}

///|
fn remove_at(node : Node, key : Int, level : Int) -> Node? {
  match node {
    Flat(key1) => if key == key1 { None } else { Some(node) }
    Leaf(head, bucket) =>
      if key == head {
        match bucket {
          Empty => None
          More(next, rest) => Some(Leaf(next, rest))
        }
      } else {
        let (removed, new_bucket) = bucket_remove(bucket, key)
        if removed {
          Some(Leaf(head, new_bucket))
        } else {
          Some(node)
        }
      }
    Branch(children) => {
      let idx = slot(key, level)
      match children_get(children, idx) {
        None => Some(node)
        Some(child) =>
          match remove_at(child, key, level + 1) {
            None =>
              if children_length(children) == 1 {
                None
              } else {
                Some(collapse_branch(children_remove(children, idx)))
              }
            Some(new_child) => {
              let new_children = children_replace(children, idx, new_child)
              Some(collapse_branch(new_children))
            }
          }
      }
    }
  }
}

///|
fn node_size(node : Node) -> Int {
  match node {
    Flat(_) => 1
    Leaf(_, bucket) => 1 + bucket_length(bucket)
    Branch(children) =>
      for i = 0, total = 0; i < children.data.length(); {
        continue i + 1, total + node_size(children.data[i])
      } nobreak {
        total
      }
  }
}

///|
pub fn new() -> HashSet {
  { root: None }
}

///|
pub fn contains(set : HashSet, key : Int) -> Bool {
  match set.root {
    None => false
    Some(node) => contains_at(node, key, 0)
  }
}

///|
pub fn add(set : HashSet, key : Int) -> HashSet {
  match set.root {
    None => { root: Some(Flat(key)) }
    Some(node) => { root: Some(add_at(node, key, 0)) }
  }
}

///|
pub fn remove(set : HashSet, key : Int) -> HashSet {
  match set.root {
    None => set
    Some(node) => { root: remove_at(node, key, 0) }
  }
}

///|
pub fn is_empty(set : HashSet) -> Bool {
  set.root is None
}

///|
pub fn length(set : HashSet) -> Int {
  match set.root {
    None => 0
    Some(node) => node_size(node)
  }
}

///|
pub fn HashSet::contains(self : HashSet, key : Int) -> Bool {
  contains(self, key)
}

///|
pub fn HashSet::add(self : HashSet, key : Int) -> HashSet {
  add(self, key)
}

///|
pub fn HashSet::remove(self : HashSet, key : Int) -> HashSet {
  remove(self, key)
}

///|
pub fn HashSet::is_empty(self : HashSet) -> Bool {
  is_empty(self)
}

///|
pub fn HashSet::length(self : HashSet) -> Int {
  length(self)
}
