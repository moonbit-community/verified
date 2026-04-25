///|
pub struct Stream {
  total : Int
  released : Int
  start : Int
  duration : Int
} derive(Eq)

///|
#proof_pure
fn vested_at(total : Int, start : Int, duration : Int, now : Int) -> Int {
  if now <= start {
    0
  } else if start + duration <= now {
    total
  } else {
    total * (now - start) / duration
  }
}

///|
pub fn create_stream(
  total : Int,
  start : Int,
  duration : Int,
) -> Stream where {
  proof_require: 0 <= total,
  proof_require: 0 < duration,
  proof_ensure: result => stream_inv(result),
} {
  let result = { total, released: 0, start, duration }
  proof_assert stream_inv(result)
  result
}

///|
pub fn vested_amount(
  total : Int,
  start : Int,
  duration : Int,
  now : Int,
) -> Int where {
  proof_require: 0 <= total,
  proof_require: 0 < duration,
  proof_ensure: result => {
    vested_amount_post(total, start, duration, now, result)
  },
} {
  let result = if now <= start {
    let result = 0
    proof_assert 0 <= result
    proof_assert result <= total
    result
  } else if start + duration <= now {
    let result = total
    proof_assert 0 <= result
    proof_assert result <= total
    result
  } else {
    let elapsed = now - start
    proof_assert start < now
    proof_assert now < start + duration
    proof_assert 0 < elapsed
    proof_assert elapsed < duration
    proof_assert 0 <= total * elapsed
    proof_assert total * elapsed <= total * duration
    let result = total * elapsed / duration
    proof_assert 0 <= result
    proof_assert result <= total
    result
  }
  proof_assert vested_amount_post(total, start, duration, now, result)
  result
}

///|
pub fn claimable(
  stream : Stream,
  now : Int,
) -> Int where {
  proof_require: stream_inv(stream),
  proof_ensure: result => claimable_post(stream, now, result),
} {
  let vested = vested_at(stream.total, stream.start, stream.duration, now)
  let result = if vested <= stream.released {
    0
  } else {
    vested - stream.released
  }
  proof_assert claimable_post(stream, now, result)
  result
}

///|
pub fn release(
  stream : Stream,
  now : Int,
) -> Stream where {
  proof_require: stream_inv(stream),
  proof_ensure: result => release_post(stream, now, result),
} {
  let vested = vested_at(stream.total, stream.start, stream.duration, now)
  let released = if vested <= stream.released {
    stream.released
  } else {
    vested
  }
  let result = {
    total: stream.total,
    released,
    start: stream.start,
    duration: stream.duration,
  }
  proof_assert release_post(stream, now, result)
  result
}
