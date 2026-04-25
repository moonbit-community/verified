///|
fn[T] new_branch_left(leaf : ReadOnlyArray[T], shift : Int) -> Tree[T] {
  match shift {
    0 => Leaf(leaf)
    s => Node([new_branch_left(leaf, s - num_bits)], None)
  }
}

///|
fn[T] Tree::size(self : Tree[T], shift : Int) -> Int {
  match self {
    Empty => 0
    Leaf(l) => l.length()
    Node(_, Some(sizes)) => sizes[sizes.length() - 1]
    Node(children, None) => {
      let len_1 = children.length() - 1
      (len_1 << shift) + children[len_1].size(shift - num_bits)
    }
  }
}

///|
fn[T] compute_sizes(
  children : ReadOnlyArray[Tree[T]],
  shift : Int,
) -> ReadOnlyArray[Int]? {
  let len = children.length()
  let sizes = ReadOnlyArray::makei(len, fn(i) {
    let mut sum = 0
    for j in 0..<=i {
      sum += children[j].size(shift)
    }
    sum
  })
  let full_subtree_size = branching_factor << shift
  let all_full = for i = 0, ok = true; i < len; {
    continue i + 1, ok && children[i].size(shift) == full_subtree_size
  } nobreak {
    ok
  }
  if all_full {
    None
  } else {
    Some(sizes)
  }
}
