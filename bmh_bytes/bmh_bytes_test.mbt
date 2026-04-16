test "empty needle matches at zero" {
  assert_eq(boyer_moore_horspool_find(b"abc", b""), Some(0))
}

test "missing needle returns none" {
  assert_eq(boyer_moore_horspool_find(b"abc", b"z"), None)
}

test "finds first occurrence" {
  assert_eq(boyer_moore_horspool_find(b"ababa", b"aba"), Some(0))
}

test "finds later occurrence" {
  assert_eq(boyer_moore_horspool_find(b"zzabcxx", b"abc"), Some(2))
}
