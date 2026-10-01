///|
using @seq {type Seq}

///|
pub enum List[T] {
  Nil
  Cons(T, List[T])
} derive(Debug)

///|
#deprecated
pub extend List with @debug.Debug::{to_repr}

///|
pub struct Deque[T] {
  front : List[T]
  back : List[T]
  len : Int
} derive(Debug)

///|
#deprecated
pub extend Deque with @debug.Debug::{to_repr}

///|
fn[T] reverse_append(
  xs : List[T],
  acc : List[T],
) -> List[T] where {
  proof_decrease: xs,
  proof_ensure: result => reverse_append_post(xs, acc, result),
} {
  match xs {
    Nil => {
      proof_assert reverse_append_post(xs, acc, acc)
      acc
    }
    Cons(value, rest) => {
      let result = reverse_append(rest, Cons(value, acc))
      proof_assert reverse_append_post(rest, Cons(value, acc), result)
      proof_assert reverse_append_post(xs, acc, result)
      result
    }
  }
}

///|
fn[T] reverse(
  xs : List[T],
) -> List[T] where {
  proof_ensure: result => reverse_post(xs, result),
} {
  let result = reverse_append(xs, Nil)
  proof_assert reverse_append_post(xs, Nil, result)
  proof_assert reverse_post(xs, result)
  result
}

///|
fn[T] normalize_front(
  d : Deque[T],
) -> Deque[T] where {
  proof_require: deque_raw_inv(d),
  proof_ensure: result => normalize_front_post(d, result),
} {
  match d.front {
    Nil =>
      match d.back {
        Nil => {
          proof_assert front_ready(d)
          proof_assert normalize_front_post(d, d)
          d
        }
        _ => {
          let front = reverse(d.back)
          proof_assert reverse_post(d.back, front)
          let result = { front, back: Nil, len: d.len, }
          proof_assert deque_raw_inv(result)
          proof_assert front_ready(result)
          proof_assert result.model() == d.model()
          proof_assert normalize_front_post(d, result)
          result
        }
      }
    _ => {
      proof_assert front_ready(d)
      proof_assert normalize_front_post(d, d)
      d
    }
  }
}

///|
fn[T] normalize_back(
  d : Deque[T],
) -> Deque[T] where {
  proof_require: deque_raw_inv(d),
  proof_ensure: result => normalize_back_post(d, result),
} {
  match d.back {
    Nil =>
      match d.front {
        Nil => {
          proof_assert back_ready(d)
          proof_assert normalize_back_post(d, d)
          d
        }
        _ => {
          let back = reverse(d.front)
          proof_assert reverse_post(d.front, back)
          let result = { front: Nil, back, len: d.len, }
          proof_assert deque_raw_inv(result)
          proof_assert back_ready(result)
          proof_assert result.model() == d.model()
          proof_assert normalize_back_post(d, result)
          result
        }
      }
    _ => {
      proof_assert back_ready(d)
      proof_assert normalize_back_post(d, d)
      d
    }
  }
}

///|
pub fn[T] empty() -> Deque[T] where {
  proof_ensure: result => empty_post(result),
} {
  let result = { front: Nil, back: Nil, len: 0, }
  proof_assert deque_inv(result)
  proof_assert empty_post(result)
  result
}

///|
pub fn[T] length(
  d : Deque[T],
) -> Int where {
  proof_require: deque_inv(d),
  proof_ensure: result => length_post(d, result),
} {
  d.len
}

///|
pub fn[T] is_empty(
  d : Deque[T],
) -> Bool where {
  proof_require: deque_inv(d),
  proof_ensure: result => is_empty_post(d, result),
} {
  d.len == 0
}

///|
pub fn[T] push_front(
  d : Deque[T],
  value : T,
) -> Deque[T] where {
  proof_require: deque_inv(d),
  proof_ensure: result => push_front_post(d, value, result),
} {
  let result = { front: Cons(value, d.front), back: d.back, len: d.len + 1, }
  proof_assert deque_inv(result)
  proof_assert push_front_post(d, value, result)
  result
}

///|
pub fn[T] push_back(
  d : Deque[T],
  value : T,
) -> Deque[T] where {
  proof_require: deque_inv(d),
  proof_ensure: result => push_back_post(d, value, result),
} {
  let result = { front: d.front, back: Cons(value, d.back), len: d.len + 1, }
  proof_assert deque_inv(result)
  proof_assert push_back_post(d, value, result)
  result
}

///|
pub fn[T : Eq] peek_front(
  d : Deque[T],
) -> T? where {
  proof_require: deque_inv(d),
  proof_ensure: result => peek_front_post(d, result),
} {
  let ready = normalize_front(d)
  proof_assert normalize_front_post(d, ready)
  match ready.front {
    Nil => {
      let result = None
      proof_assert peek_front_post(d, result)
      result
    }
    Cons(value, _) => {
      let result = Some(value)
      proof_assert peek_front_post(d, result)
      result
    }
  }
}

///|
pub fn[T : Eq] pop_front(
  d : Deque[T],
) -> (T, Deque[T])? where {
  proof_require: deque_inv(d),
  proof_ensure: result => pop_front_post(d, result),
} {
  let ready = normalize_front(d)
  proof_assert normalize_front_post(d, ready)
  match ready.front {
    Nil => None
    Cons(value, rest) => {
      let next = { front: rest, back: ready.back, len: ready.len - 1, }
      proof_assert deque_inv(next)
      let result = Some((value, next))
      proof_assert pop_front_post(d, result)
      result
    }
  }
}

///|
pub fn[T : Eq] peek_back(
  d : Deque[T],
) -> T? where {
  proof_require: deque_inv(d),
  proof_ensure: result => peek_back_post(d, result),
} {
  let ready = normalize_back(d)
  proof_assert normalize_back_post(d, ready)
  match ready.back {
    Nil => {
      let result = None
      proof_assert peek_back_post(d, result)
      result
    }
    Cons(value, _) => {
      let result = Some(value)
      proof_assert peek_back_post(d, result)
      result
    }
  }
}

///|
pub fn[T : Eq] pop_back(
  d : Deque[T],
) -> (T, Deque[T])? where {
  proof_require: deque_inv(d),
  proof_ensure: result => pop_back_post(d, result),
} {
  let ready = normalize_back(d)
  proof_assert normalize_back_post(d, ready)
  match ready.back {
    Nil => None
    Cons(value, rest) => {
      let next = { front: ready.front, back: rest, len: ready.len - 1, }
      proof_assert deque_inv(next)
      let result = Some((value, next))
      proof_assert pop_back_post(d, result)
      result
    }
  }
}
