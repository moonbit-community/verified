///|
fn repeat_path(value : Int, n : Int) -> Path {
  if n <= 0 {
    Nil
  } else {
    Cons(value, repeat_path(value, n - 1))
  }
}

///|
test "bit 0 chooses right child when key bit is zero" {
  let path = Cons(9, Nil)
  assert_eq(compute_root_from(0U, 0, 5, path), 371)
}

///|
test "bit 0 chooses left child when key bit is one" {
  let path = Cons(9, Nil)
  assert_eq(compute_root_from(1U, 0, 5, path), 315)
}

///|
test "verify recomputes full 32-step root exactly" {
  let path = repeat_path(1, 32)
  let root = compute_root(0U, 7, path)
  assert_eq(verify(root, 0U, 7, path), true)
  assert_eq(verify(root + 1, 0U, 7, path), false)
}
