///|
test "empty tree stores zero at every key" {
  let tree = empty()
  assert_eq(lookup(tree, 0U), 0)
  assert_eq(lookup(tree, 7U), 0)
}

///|
test "updating empty tree sets the selected leaf" {
  let tree = update(empty(), 0U, 7)
  assert_eq(lookup(tree, 0U), 7)
  assert_eq(lookup(tree, 1U), 0)
}

///|
test "multiple updates preserve previously written leaves" {
  let tree0 = empty()
  let tree1 = update(tree0, 0U, 7)
  let tree2 = update(tree1, 1U, 9)
  let tree3 = update(tree2, 0U, 4)
  assert_eq(lookup(tree2, 0U), 7)
  assert_eq(lookup(tree2, 1U), 9)
  assert_eq(lookup(tree3, 0U), 4)
  assert_eq(lookup(tree3, 1U), 9)
}

///|
test "writing zero into empty tree keeps the empty root" {
  let tree0 = empty()
  let tree1 = update(tree0, 5U, 0)
  assert_eq(root(tree1), root(tree0))
  assert_eq(lookup(tree1, 5U), 0)
}
