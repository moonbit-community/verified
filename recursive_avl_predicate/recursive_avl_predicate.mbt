///|
priv enum Tree {
  Empty
  Node(Tree, Int, Tree, Int)
}

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
#requires(avl(t))
#ensures(nonneg(result))
fn get_height(t : Tree) -> Int {
  height(t)
}
