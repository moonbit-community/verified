///|
priv enum Tree {
  Empty
  Node(Tree)
}

///|
#ensures(avl(result))
fn empty() -> Tree {
  Empty
}
