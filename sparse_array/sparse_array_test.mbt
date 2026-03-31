///|
test "empty lookup" {
  let sa = empty()
  assert_eq(get(sa, 0), None)
  assert_eq(length(sa), 0)
}

///|
test "singleton lookup" {
  let sa = singleton(7, 70)
  assert_eq(get(sa, 7), Some(70))
  assert_eq(get(sa, 6), None)
  assert_eq(length(sa), 1)
}

///|
test "add inserts at lower middle and upper positions" {
  let sa = add(add(add(add(empty(), 10, 100), 3, 30), 31, 310), 7, 70)
  assert_eq(get(sa, 3), Some(30))
  assert_eq(get(sa, 7), Some(70))
  assert_eq(get(sa, 10), Some(100))
  assert_eq(get(sa, 31), Some(310))
  assert_eq(length(sa), 4)
}

///|
test "replace preserves other entries" {
  let sa = add(add(add(empty(), 2, 20), 8, 80), 15, 150)
  let replaced = replace(sa, 8, 81)
  assert_eq(get(replaced, 2), Some(20))
  assert_eq(get(replaced, 8), Some(81))
  assert_eq(get(replaced, 15), Some(150))
  assert_eq(length(replaced), 3)
}

///|
test "remove first middle and last entries" {
  let sa = add(add(add(add(empty(), 1, 10), 8, 80), 20, 200), 31, 310)
  let no_first = remove(sa, 1)
  assert_eq(get(no_first, 1), None)
  assert_eq(get(no_first, 8), Some(80))
  let no_middle = remove(no_first, 20)
  assert_eq(get(no_middle, 20), None)
  assert_eq(get(no_middle, 8), Some(80))
  let no_last = remove(no_middle, 31)
  assert_eq(get(no_last, 31), None)
  assert_eq(get(no_last, 8), Some(80))
  assert_eq(length(no_last), 1)
}

///|
test "remove singleton returns empty" {
  let sa = remove(singleton(5, 50), 5)
  assert_eq(get(sa, 5), None)
  assert_eq(length(sa), 0)
}

///|
test "top level and method surfaces agree" {
  let sa = empty().add(0, 11).add(31, 99)
  assert_eq(get(sa, 0), sa.get(0))
  assert_eq(get(sa, 31), sa.get(31))
  assert_eq(length(sa), sa.length())
}
