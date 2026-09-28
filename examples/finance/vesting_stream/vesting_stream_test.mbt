///|
test "nothing is claimable before the cliff starts" {
  let stream = @vesting_stream.create_stream(1_000, 10, 100)
  assert_eq(@vesting_stream.vested_amount(stream.total, stream.start, stream.duration, 5), 0)
  assert_eq(@vesting_stream.claimable(stream, 5), 0)
}

///|
test "mid-stream release tracks linear vesting" {
  let stream = @vesting_stream.create_stream(1_000, 10, 100)
  let released = @vesting_stream.release(stream, 60)
  assert_eq(released.released, 500)
  assert_eq(@vesting_stream.claimable(released, 60), 0)
}

///|
test "full release caps at the total allocation" {
  let stream = @vesting_stream.create_stream(1_000, 10, 100)
  let released = @vesting_stream.release(stream, 200)
  assert_eq(released.released, 1_000)
  assert_eq(@vesting_stream.claimable(released, 200), 0)
}
