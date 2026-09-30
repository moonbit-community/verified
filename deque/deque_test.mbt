///|
test "batched deque supports both ends" {
  let d0 : @deque.Deque[Int] = @deque.empty()
  assert_eq(@deque.is_empty(d0), true)

  let d1 = @deque.push_front(@deque.push_back(@deque.push_front(@deque.push_back(d0, 2), 1), 3), 0)
  assert_eq(@deque.length(d1), 4)
  match @deque.peek_front(d1) {
    Some(value) => assert_eq(value, 0)
    None => abort("expected front peek")
  }
  match @deque.peek_back(d1) {
    Some(value) => assert_eq(value, 3)
    None => abort("expected back peek")
  }

  let (a, d2) = match @deque.pop_front(d1) {
    Some(pair) => pair
    None => abort("expected front")
  }
  let (b, d3) = match @deque.pop_back(d2) {
    Some(pair) => pair
    None => abort("expected back")
  }
  let (c, d4) = match @deque.pop_front(d3) {
    Some(pair) => pair
    None => abort("expected front")
  }
  let (d, d5) = match @deque.pop_back(d4) {
    Some(pair) => pair
    None => abort("expected back")
  }

  assert_eq(a, 0)
  assert_eq(b, 3)
  assert_eq(c, 1)
  assert_eq(d, 2)
  match @deque.pop_front(d5) {
    None => ()
    Some(_) => abort("expected empty deque front")
  }
  match @deque.pop_back(d5) {
    None => ()
    Some(_) => abort("expected empty deque back")
  }
}
