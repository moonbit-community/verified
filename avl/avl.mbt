///|
using @fset {type Fset}

///|
pub enum Tree {
  Empty
  Node(Tree, Int, Tree, Int)
}

///|
#proof_pure
fn height(t : Tree) -> Int {
  match t {
    Empty => 0
    Node(_, _, _, h) => h
  }
}

///|
#proof_pure
fn max2(a : Int, b : Int) -> Int {
  if a < b {
    b
  } else {
    a
  }
}

///|
pub fn empty() -> Tree {
  Empty
}

///|
fn mk(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: avl_inv(l),
  proof_require: avl_inv(r),
  proof_require: all_lt(elements(l), x),
  proof_require: all_gt(x, elements(r)),
  proof_require: balanced_heights(l, r),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => {
    elements(result).eq(elements(l).union(elements(r)).add(x))
  },
  proof_ensure: result => mk_height_post(l, r, result),
} {
  Node(l, x, r, 1 + max2(height(l), height(r)))
}

///|
pub fn contains(x : Int, t : Tree) -> Bool {
  match t {
    Empty => false
    Node(l, y, r, _) =>
      if x < y {
        contains(x, l)
      } else if y < x {
        contains(x, r)
      } else {
        true
      }
  }
}

///|
fn balance_left_double(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: balance_pre(l, x, r),
  proof_require: left_heavy(l, r),
  proof_require: left_double_case(l),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => balance_elements_post(l, x, r, result),
  proof_ensure: result => balance_height_upper_post(l, r, result),
  proof_ensure: result => balance_height_lower_post(l, r, result),
} {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) =>
      match lr {
        Empty => panic()
        Node(lrl, lrx, lrr, _) => {
          proof_assert elements(l).mem(lrx)
          proof_assert lx < lrx
          proof_assert lrx < x
          proof_assert all_gt(lrx, elements(r))
          proof_assert -1 <= height(ll) - height(lrl) &&
            height(ll) - height(lrl) <= 1
          proof_assert elements_subset(lrl, lr)
          proof_assert all_gt(lx, elements(lrl))
          proof_assert all_lt(elements(ll), lx) && all_gt(lx, elements(lrl))
          let nl = mk(ll, lx, lrl)
          proof_assert elements(nl).eq(
            elements(ll).union(elements(lrl)).add(lx),
          )
          proof_assert height(nl) == 1 + max2(height(ll), height(lrl))
          proof_assert elements_subset(lrr, lr)
          proof_assert all_lt(elements(lrr), x)
          proof_assert all_gt(x, elements(r))
          proof_assert -1 <= height(lrr) - height(r) &&
            height(lrr) - height(r) <= 1
          let nr = mk(lrr, x, r)
          proof_assert elements(nr).eq(elements(lrr).union(elements(r)).add(x))
          proof_assert height(nr) == 1 + max2(height(lrr), height(r))
          proof_assert all_lt(elements(nl), lrx) && all_gt(lrx, elements(nr))
          proof_assert -1 <= height(nl) - height(nr) &&
            height(nl) - height(nr) <= 1
          proof_assert elements(nl)
            .union(elements(nr))
            .add(lrx)
            .eq(elements(l).union(elements(r)).add(x))
          mk(nl, lrx, nr)
        }
      }
  }
}

///|
fn balance_right_double(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: balance_pre(l, x, r),
  proof_require: right_heavy(l, r),
  proof_require: right_double_case(r),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => balance_elements_post(l, x, r, result),
  proof_ensure: result => balance_height_upper_post(l, r, result),
  proof_ensure: result => balance_height_lower_post(l, r, result),
} {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) =>
      match rl {
        Empty => panic()
        Node(rll, rlx, rlr, _) => {
          proof_assert elements(r).mem(rlx)
          proof_assert elements_subset(rl, r)
          proof_assert elements_subset(rll, rl)
          proof_assert x < rlx
          proof_assert rlx < rx
          proof_assert all_lt(elements(l), rlx)
          proof_assert all_gt(rlx, elements(rr))
          proof_assert -1 <= height(l) - height(rll) &&
            height(l) - height(rll) <= 1
          proof_assert all_gt(x, elements(rl))
          proof_assert all_lt(elements(l), x) && all_gt(x, elements(rll))
          let nl = mk(l, x, rll)
          proof_assert elements(nl).eq(elements(l).union(elements(rll)).add(x))
          proof_assert elements_subset(rlr, rl)
          proof_assert -1 <= height(rlr) - height(rr) &&
            height(rlr) - height(rr) <= 1
          proof_assert all_lt(elements(rlr), rx) && all_gt(rx, elements(rr))
          let nr = mk(rlr, rx, rr)
          proof_assert elements(nr).eq(
            elements(rlr).union(elements(rr)).add(rx),
          )
          proof_assert all_lt(elements(nl), rlx) && all_gt(rlx, elements(nr))
          proof_assert -1 <= height(nl) - height(nr) &&
            height(nl) - height(nr) <= 1
          proof_assert double_rotation_eq_rl(
            x,
            rlx,
            rx,
            elements(l),
            elements(rll),
            elements(rlr),
            elements(rr),
          )
          proof_assert elements(nl)
            .union(elements(nr))
            .add(rlx)
            .eq(elements(l).union(elements(r)).add(x))
          mk(nl, rlx, nr)
        }
      }
  }
}

///|
fn balance(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: balance_pre(l, x, r),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => balance_elements_post(l, x, r, result),
  proof_ensure: result => balance_height_exact_post(l, r, result),
  proof_ensure: result => balance_height_upper_post(l, r, result),
  proof_ensure: result => balance_height_lower_post(l, r, result),
} {
  if height(l) > height(r) + 1 {
    proof_assert left_heavy(l, r)
    match l {
      Empty => panic()
      Node(ll, lx, lr, _) =>
        if height(ll) >= height(lr) {
          proof_assert lx < x
          proof_assert all_gt(lx, elements(r))
          proof_assert -1 <= height(lr) - height(r) &&
            height(lr) - height(r) <= 1
          proof_assert all_lt(elements(lr), x) && all_gt(x, elements(r))
          let nr = mk(lr, x, r)
          proof_assert -1 <= height(ll) - height(nr) &&
            height(ll) - height(nr) <= 1
          proof_assert elements(ll)
            .union(elements(nr))
            .add(lx)
            .eq(elements(l).union(elements(r)).add(x))
          mk(ll, lx, nr)
        } else {
          proof_assert left_double_case(l)
          balance_left_double(l, x, r)
        }
    }
  } else if height(r) > height(l) + 1 {
    proof_assert right_heavy(l, r)
    match r {
      Empty => panic()
      Node(rl, rx, rr, _) =>
        if height(rr) >= height(rl) {
          proof_assert x < rx
          proof_assert all_lt(elements(l), rx)
          proof_assert -1 <= height(l) - height(rl) &&
            height(l) - height(rl) <= 1
          proof_assert all_lt(elements(l), x) && all_gt(x, elements(rl))
          let nl = mk(l, x, rl)
          proof_assert -1 <= height(nl) - height(rr) &&
            height(nl) - height(rr) <= 1
          mk(nl, rx, rr)
        } else {
          proof_assert right_double_case(r)
          balance_right_double(l, x, r)
        }
    }
  } else {
    proof_assert balanced_heights(l, r)
    mk(l, x, r)
  }
}

///|
fn remove_min(
  t : Tree,
) -> (Int, Tree) where {
  proof_decrease: t,
  proof_require: avl_inv(t),
  proof_require: non_empty(t),
  proof_ensure: result => remove_min_post(t, result),
} {
  match t {
    Empty => panic()
    Node(l, y, r, _) =>
      match l {
        Empty => {
          proof_assert elements_subset(r, t)
          (y, r)
        }
        Node(_, _, _, _) => {
          let (m, l1) = remove_min(l)
          proof_assert m < y
          proof_assert all_gt(m, elements(r))
          proof_assert balance_pre(l1, y, r)
          let t1 = balance(l1, y, r)
          proof_assert all_gt(m, elements(l1).union(elements(r)))
          proof_assert all_gt(m, elements(t1))
          proof_assert elements(t).eq(elements(t1).add(m))
          proof_assert elements_subset(t1, t)
          (m, t1)
        }
      }
  }
}

///|
pub fn insert(
  x : Int,
  t : Tree,
) -> Tree where {
  proof_decrease: t,
  proof_require: avl_inv(t),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => insert_elements_post(x, t, result),
  proof_ensure: result => insert_height_lower_post(t, result),
  proof_ensure: result => insert_height_upper_post(t, result),
} {
  match t {
    Empty => mk(Empty, x, Empty)
    Node(l, y, r, _) =>
      if x < y {
        let l1 = insert(x, l)
        proof_assert balance_pre(l1, y, r)
        balance(l1, y, r)
      } else if y < x {
        let r1 = insert(x, r)
        proof_assert balance_pre(l, y, r1)
        balance(l, y, r1)
      } else {
        t
      }
  }
}

///|
pub fn delete(
  x : Int,
  t : Tree,
) -> Tree where {
  proof_decrease: t,
  proof_require: avl_inv(t),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => delete_elements_post(x, t, result),
  proof_ensure: result => delete_height_lower_post(t, result),
  proof_ensure: result => delete_height_upper_post(t, result),
} {
  match t {
    Empty => {
      proof_assert delete_elements_post(x, t, Empty)
      Empty
    }
    Node(l, y, r, _) =>
      if x < y {
        let l1 = delete(x, l)
        proof_assert balance_pre(l1, y, r)
        let t1 = balance(l1, y, r)
        proof_assert elements(t1).eq(
          elements(l).remove(x).union(elements(r)).add(y),
        )
        proof_assert delete_elements_post(x, t, t1)
        t1
      } else if y < x {
        let r1 = delete(x, r)
        proof_assert balance_pre(l, y, r1)
        let t1 = balance(l, y, r1)
        proof_assert elements(t1).eq(
          elements(l).union(elements(r).remove(x)).add(y),
        )
        proof_assert delete_elements_post(x, t, t1)
        t1
      } else {
        match r {
          Empty => {
            proof_assert delete_elements_post(x, t, l)
            l
          }
          Node(_, _, _, _) => {
            let (s, r1) = remove_min(r)
            proof_assert y < s
            proof_assert all_lt(elements(l), s)
            proof_assert balance_pre(l, s, r1)
            let t1 = balance(l, s, r1)
            proof_assert delete_elements_post(x, t, t1)
            t1
          }
        }
      }
  }
}
