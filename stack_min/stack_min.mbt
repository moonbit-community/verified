///|
/// A min stack caches the minimum in each cell, so the top element is enough
/// to answer `min_value` in O(1). The proof invariant is local: every node
/// must keep the cached minimum equal to a value that really occurs in the
/// whole suffix beneath it.
pub enum MinStack {
  Nil
  Cons(Int, Int, MinStack)
}

///|
fn stack_size(s : MinStack) -> Int {
  match s {
    Nil => 0
    Cons(_, _, tail) => 1 + stack_size(tail)
  }
}

///|
/// Empty is valid because the invariant is vacuous on `Nil`.
pub fn empty() -> MinStack where { proof_ensure: result => stack_inv(result) } {
  Nil
}

///|
/// `size` is just the structural length of the spine; it does not depend on
/// the cached minimum fields.
pub fn size(s : MinStack) -> Int {
  stack_size(s)
}

///|
/// The proof obligation here is only to read the cached minimum from the top
/// cell and discharge that it really is the minimum for the whole stack.
pub fn min_value(
  s : MinStack,
) -> Int? where {
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
/// Pushing only changes the new head. The old stack invariant supplies the
/// previous minimum, and the new cache is just `min(value, old_min)` with the
/// empty-stack case handled separately.
pub fn push(
  s : MinStack,
  value : Int,
) -> MinStack where {
  proof_require: stack_inv(s),
  proof_ensure: result => push_post(s, value, result),
} {
  let new_min = match s {
    Nil => value
    Cons(_, min, _) => if value < min { value } else { min }
  }
  let result = Cons(value, new_min, s)
  proof_assert stack_inv(result)
  proof_assert count(result, value) == count(s, value) + 1
  proof_assert ∀ y : Int, y != value → count(result, y) == count(s, y)
  proof_assert push_post(s, value, result)
  result
}

///|
/// Popping forgets exactly one cell. The returned tail already satisfied the
/// invariant, so the proof is a straight reuse of the existing suffix.
pub fn pop(
  s : MinStack,
) -> (Int, MinStack)? where {
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
/// Folding from right to left is the proof-friendly direction here: each
/// `push` sees a stack that already satisfies the invariant, so the cached
/// minimum is rebuilt incrementally.
pub fn from_array(arr : ArrayView[Int]) -> MinStack {
  arr.rev_fold(init=Nil, (st, value) => push(st, value))
}
