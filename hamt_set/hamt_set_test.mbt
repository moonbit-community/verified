///|
test "new empty contains length" {
  let s = new()
  assert_true(s.is_empty())
  assert_eq(s.length(), 0)
  assert_false(s.contains(1))
}

///|
test "add singleton and duplicate" {
  let s = new().add(5).add(5)
  assert_false(s.is_empty())
  assert_true(s.contains(5))
  assert_eq(s.length(), 1)
}

///|
test "remove absent and present" {
  let s = new().add(1).add(2)
  let s1 = s.remove(3)
  assert_eq(s1.length(), 2)
  let s2 = s1.remove(2)
  assert_true(s2.contains(1))
  assert_false(s2.contains(2))
  assert_eq(s2.length(), 1)
}

///|
test "branch creation different first slot" {
  let s = new().add(1).add(2)
  assert_true(s.contains(1))
  assert_true(s.contains(2))
  assert_eq(s.length(), 2)
}

///|
test "deeper join" {
  let a = 1
  let b = 1 + 32
  let s = new().add(a).add(b)
  assert_true(s.contains(a))
  assert_true(s.contains(b))
  assert_eq(s.length(), 2)
}

///|
test "leaf collision bucket" {
  let a = 0
  let b = 1
  let s = new().add(a).add(b)
  assert_true(s.contains(a))
  assert_true(s.contains(b))
  assert_eq(s.length(), 2)
}

///|
test "branch collapse after remove" {
  let a = 1
  let b = 2
  let s = new().add(a).add(b).remove(b)
  assert_true(s.contains(a))
  assert_false(s.contains(b))
  assert_eq(s.length(), 1)
}
