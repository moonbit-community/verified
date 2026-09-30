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
pub struct Queue[T] {
  front : List[T]
  rear : List[T]
  len : Int
} derive(Debug)

///|
#deprecated
pub extend Queue with @debug.Debug::{to_repr}

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
fn[T] normalize(
  q : Queue[T],
) -> Queue[T] where {
  proof_require: queue_raw_inv(q),
  proof_ensure: result => normalize_post(q, result),
} {
  match q.front {
    Nil =>
      match q.rear {
        Nil => {
          proof_assert queue_inv(q)
          proof_assert normalize_post(q, q)
          q
        }
        _ => {
          let front = reverse(q.rear)
          proof_assert reverse_post(q.rear, front)
          let result = { front, rear: Nil, len: q.len }
          proof_assert queue_inv(result)
          proof_assert result.model() == q.model()
          proof_assert normalize_post(q, result)
          result
        }
      }
    _ => {
      proof_assert queue_inv(q)
      proof_assert normalize_post(q, q)
      q
    }
  }
}

///|
pub fn[T] empty() -> Queue[T] where {
  proof_ensure: result => empty_post(result),
} {
  let result = { front: Nil, rear: Nil, len: 0 }
  proof_assert queue_inv(result)
  proof_assert empty_post(result)
  result
}

///|
pub fn[T] length(
  q : Queue[T],
) -> Int where {
  proof_require: queue_inv(q),
  proof_ensure: result => length_post(q, result),
} {
  q.len
}

///|
pub fn[T] is_empty(
  q : Queue[T],
) -> Bool where {
  proof_require: queue_inv(q),
  proof_ensure: result => is_empty_post(q, result),
} {
  q.len == 0
}

///|
pub fn[T] push_back(
  q : Queue[T],
  value : T,
) -> Queue[T] where {
  proof_require: queue_inv(q),
  proof_ensure: result => push_back_post(q, value, result),
} {
  let pending = { front: q.front, rear: Cons(value, q.rear), len: q.len + 1 }
  proof_assert queue_raw_inv(pending)
  let result = normalize(pending)
  proof_assert normalize_post(pending, result)
  proof_assert push_back_post(q, value, result)
  result
}

///|
pub fn[T : Eq] peek(
  q : Queue[T],
) -> T? where {
  proof_require: queue_inv(q),
  proof_ensure: result => peek_post(q, result),
} {
  match q.front {
    Nil => None
    Cons(value, _) => Some(value)
  }
}

///|
pub fn[T : Eq] pop_front(
  q : Queue[T],
) -> (T, Queue[T])? where {
  proof_require: queue_inv(q),
  proof_ensure: result => pop_front_post(q, result),
} {
  match q.front {
    Nil => None
    Cons(value, rest) => {
      let pending = { front: rest, rear: q.rear, len: q.len - 1 }
      proof_assert queue_raw_inv(pending)
      let next = normalize(pending)
      proof_assert normalize_post(pending, next)
      let result = Some((value, next))
      proof_assert pop_front_post(q, result)
      result
    }
  }
}
