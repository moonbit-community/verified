///|
fn build_range(count : Int) -> Vector[Int] {
  for i = 0, v = Vector::new(); i < count; {
    continue i + 1, v.push(i)
  } nobreak {
    v
  }
}

///|
fn snapshot(v : Vector[Int]) -> Array[Int] {
  let out = []
  for i in 0..<v.length() {
    out.push(v[i])
  }
  out
}

///|
test "empty and singleton operations" {
  let empty : Vector[Int] = Vector::new()
  assert_eq(empty.is_empty(), true)
  assert_eq(empty.peek(), None)
  match empty.pop() {
    None => ()
    Some(_) => abort("empty pop should return None")
  }

  let one = empty.push(7)
  assert_eq(one.is_empty(), false)
  assert_eq(one.length(), 1)
  assert_eq(one.peek(), Some(7))
  assert_eq(snapshot(one), [7])
  assert_eq(one.pop().unwrap().is_empty(), true)
}

///|
test "lookup and update on small vectors" {
  let values = build_range(5)
  assert_eq(values.length(), 5)
  assert_eq(values.get(-1), None)
  assert_eq(values.get(5), None)
  assert_eq(values.get(0), Some(0))
  assert_eq(values.get(4), Some(4))

  let updated = values.set(2, 20)
  assert_eq(snapshot(updated), [0, 1, 20, 3, 4])
}

///|
test "set in tree prefix and tail" {
  let values = build_range(40)
  let updated = values.set(5, 500).set(35, 3500)
  let expected = Array::makei(40, fn(i) { i })
  expected[5] = 500
  expected[35] = 3500
  assert_eq(snapshot(updated), expected)
}

///|
test "push across tail boundary" {
  let v31 = build_range(31)
  let v32 = build_range(32)
  let v33 = build_range(33)

  assert_eq(v31.length(), 31)
  assert_eq(v32.length(), 32)
  assert_eq(v33.length(), 33)
  assert_eq(v32.peek(), Some(31))
  assert_eq(v33.peek(), Some(32))
  assert_eq(v33[0], 0)
  assert_eq(v33[31], 31)
  assert_eq(v33[32], 32)
}

///|
test "push to forty and read back" {
  let values = build_range(40)
  assert_eq(values.length(), 40)
  assert_eq(values[0], 0)
  assert_eq(values[31], 31)
  assert_eq(values[32], 32)
  assert_eq(values[39], 39)
  assert_eq(snapshot(values), Array::makei(40, fn(i) { i }))
}

///|
test "pop from tail and across boundary" {
  let values = build_range(40)
  let popped = values.pop().unwrap()
  assert_eq(popped.length(), 39)
  assert_eq(snapshot(popped), Array::makei(39, fn(i) { i }))

  let boundary = build_range(33)
  let boundary_popped = boundary.pop().unwrap()
  assert_eq(boundary_popped.length(), 32)
  assert_eq(snapshot(boundary_popped), Array::makei(32, fn(i) { i }))
}

///|
test "repeated pop to empty" {
  let mut values = build_range(10)
  for remaining in 0..<10 {
    assert_eq(values.length(), 10 - remaining)
    values = values.pop().unwrap()
  }
  assert_eq(values.is_empty(), true)
}

///|
test "observational sequences" {
  let base = build_range(12)
  let after_set = base.set(3, 30).set(10, 100)
  assert_eq(snapshot(after_set), [0, 1, 2, 30, 4, 5, 6, 7, 8, 9, 100, 11])

  let after_pop = after_set.pop().unwrap().pop().unwrap()
  assert_eq(snapshot(after_pop), [0, 1, 2, 30, 4, 5, 6, 7, 8, 9])
}
