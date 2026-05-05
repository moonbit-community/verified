///|
test "batched queue preserves FIFO order" {
  let q0 : @queue.Queue[Int] = @queue.empty()
  assert_eq(@queue.length(q0), 0)
  assert_eq(@queue.is_empty(q0), true)

  let q1 = @queue.push_back(@queue.push_back(@queue.push_back(q0, 1), 2), 3)
  assert_eq(@queue.length(q1), 3)
  match @queue.peek(q1) {
    Some(value) => assert_eq(value, 1)
    None => abort("expected first peek")
  }

  let (a, q2) = match @queue.pop_front(q1) {
    Some(pair) => pair
    None => abort("expected first value")
  }
  let (b, q3) = match @queue.pop_front(q2) {
    Some(pair) => pair
    None => abort("expected second value")
  }
  let q4 = @queue.push_back(q3, 4)
  let (c, q5) = match @queue.pop_front(q4) {
    Some(pair) => pair
    None => abort("expected third value")
  }
  let (d, q6) = match @queue.pop_front(q5) {
    Some(pair) => pair
    None => abort("expected fourth value")
  }

  assert_eq(a, 1)
  assert_eq(b, 2)
  assert_eq(c, 3)
  assert_eq(d, 4)
  match @queue.pop_front(q6) {
    None => ()
    Some(_) => abort("expected empty queue")
  }
}
