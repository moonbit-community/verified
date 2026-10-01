///|
test "empty needle matches at zero" {
  @debug.assert_eq(@bmh_bytes.boyer_moore_horspool_find(b"abc", b""), Some(0))
}

///|
test "missing needle returns none" {
  @debug.assert_eq(@bmh_bytes.boyer_moore_horspool_find(b"abc", b"z"), None)
}

///|
test "finds first occurrence" {
  @debug.assert_eq(
    @bmh_bytes.boyer_moore_horspool_find(b"ababa", b"aba"),
    Some(0),
  )
}

///|
test "finds later occurrence" {
  @debug.assert_eq(
    @bmh_bytes.boyer_moore_horspool_find(b"zzabcxx", b"abc"),
    Some(2),
  )
}
