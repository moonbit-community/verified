///|
test "empty lookup" {
  let sa = empty()
  assert_eq(sa.get(0), None)
  assert_eq(sa.length(), 0)
}

///|
test "singleton lookup" {
  let sa = singleton(7, 70)
  assert_eq(sa.get(7), Some(70))
  assert_eq(sa.get(6), None)
  assert_eq(sa.length(), 1)
}

///|
test "add inserts at lower middle and upper positions" {
  let sa = empty().add(10, 100).add(3, 30).add(31, 310).add(7, 70)
  assert_eq(sa.get(3), Some(30))
  assert_eq(sa.get(7), Some(70))
  assert_eq(sa.get(10), Some(100))
  assert_eq(sa.get(31), Some(310))
  assert_eq(sa.length(), 4)
}

///|
test "replace preserves other entries" {
  let sa = empty().add(2, 20).add(8, 80).add(15, 150)
  let replaced = sa.replace(8, 81)
  assert_eq(replaced.get(2), Some(20))
  assert_eq(replaced.get(8), Some(81))
  assert_eq(replaced.get(15), Some(150))
  assert_eq(replaced.length(), 3)
}

///|
test "remove first middle and last entries" {
  let sa = empty().add(1, 10).add(8, 80).add(20, 200).add(31, 310)
  let no_first = sa.remove(1)
  assert_eq(no_first.get(1), None)
  assert_eq(no_first.get(8), Some(80))
  let no_middle = no_first.remove(20)
  assert_eq(no_middle.get(20), None)
  assert_eq(no_middle.get(8), Some(80))
  let no_last = no_middle.remove(31)
  assert_eq(no_last.get(31), None)
  assert_eq(no_last.get(8), Some(80))
  assert_eq(no_last.length(), 1)
}

///|
test "remove singleton returns empty" {
  let sa = singleton(5, 50).remove(5)
  assert_eq(sa.get(5), None)
  assert_eq(sa.length(), 0)
}

///|
test "method surface works" {
  let sa = empty().add(0, 11).add(31, 99)
  assert_eq(sa.get(0), Some(11))
  assert_eq(sa.get(31), Some(99))
  assert_eq(sa.length(), 2)
}
