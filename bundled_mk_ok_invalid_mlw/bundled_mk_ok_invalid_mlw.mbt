///|
priv enum Tree {
  Empty
  Node(Tree, Int, Tree, Int)
}

///|
#proof_external("set.Fset", "fset")
type Fset[T]

///|
#proof_pure
fn height(t : Tree) -> Int {
  match t {
    Empty => 0
    Node(_, _, _, h) => h
  }
}

///|
#proof_pure
fn max2(a : Int, b : Int) -> Int {
  if a < b { b } else { a }
}

///|
#requires(balanced_heights(l, r))
#requires(ordered_node(l, x, r))
#requires(avl(r))
#requires(avl(l))
#ensures(mk_ok(l, x, r, result))
fn mk(l : Tree, x : Int, r : Tree) -> Tree {
  Node(l, x, r, 1 + max2(height(l), height(r)))
}
