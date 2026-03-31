///|
pub enum MinStack {
  Nil
  Cons(Int, Int, MinStack)
} derive(Show)

///|
#proof_pure
fn min2(a : Int, b : Int) -> Int {
  if a < b {
    a
  } else {
    b
  }
}

///|
fn stack_size(s : MinStack) -> Int {
  match s {
    Nil => 0
    Cons(_, _, tail) => 1 + stack_size(tail)
  }
}

///|
pub fn empty() -> MinStack where {
  proof_ensure: result => stack_inv(result),
} {
  Nil
}

///|
pub fn size(s : MinStack) -> Int {
  stack_size(s)
}

///|
pub fn min_value(s : MinStack) -> Int? where {
  proof_require: stack_inv(s),
  proof_ensure: result => min_value_post(s, result),
} {
  match s {
    Nil => None
    Cons(_, min, _) => {
      proof_assert is_minimum(s, min)
      Some(min)
    }
  }
}

///|
pub fn push(s : MinStack, value : Int) -> MinStack where {
  proof_require: stack_inv(s),
  proof_ensure: result => push_post(s, value, result),
} {
  let new_min = match s {
    Nil => value
    Cons(_, min, _) => if value < min { value } else { min }
  }
  let result = Cons(value, new_min, s)
  proof_assert push_post(s, value, result)
  result
}

///|
pub fn pop(s : MinStack) -> (Int, MinStack)? where {
  proof_require: stack_inv(s),
  proof_ensure: result => pop_post(s, result),
} {
  match s {
    Nil => None
    Cons(value, _, tail) => {
      let result = Some((value, tail))
      proof_assert pop_post(s, result)
      result
    }
  }
}

///|
pub fn from_array(arr : ArrayView[Int]) -> MinStack {
  arr.rev_fold(init=Nil, (st, value) => push(st, value))
}
