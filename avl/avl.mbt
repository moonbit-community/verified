///|
pub enum Tree {
  Empty
  Node(Tree, Int, Tree, Int)
}

///|
#proof_external("set.Fset", "fset")
pub type Fset[T]

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
#requires(avl(l))
#requires(avl(r))
#requires(all_lt(elements(l), x))
#requires(all_gt(x, elements(r)))
#requires(balanced_heights(l, r))
#ensures(avl(result))
#ensures(fset_eq(elements(result), fset_add(x, fset_union(elements(l), elements(r)))))
#ensures(mk_height_ok(l, r, result))
fn mk(l : Tree, x : Int, r : Tree) -> Tree {
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
#requires(balance_pre(l, x, r))
#requires(left_heavy(l, r))
#requires(left_double_case(l))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_left_double(l : Tree, x : Int, r : Tree) -> Tree {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) =>
      match lr {
        Empty => panic()
        Node(lrl, lrx, lrr, _) => {
          proof_assert fset_mem(lrx, elements(l))
          proof_assert lx < lrx
          proof_assert lrx < x
          proof_assert all_gt(lrx, elements(r))
          proof_assert -1 <= height(ll) - height(lrl) &&
            height(ll) - height(lrl) <= 1
          proof_assert elements_subset(lrl, lr)
          proof_assert all_gt(lx, elements(lrl))
          proof_assert all_lt(elements(ll), lx) && all_gt(lx, elements(lrl))
          let nl = mk(ll, lx, lrl)
          proof_assert fset_eq(
            elements(nl),
            fset_add(lx, fset_union(elements(ll), elements(lrl))),
          )
          proof_assert height(nl) == 1 + max2(height(ll), height(lrl))
          proof_assert elements_subset(lrr, lr)
          proof_assert all_lt(elements(lrr), x)
          proof_assert all_gt(x, elements(r))
          proof_assert -1 <= height(lrr) - height(r) &&
            height(lrr) - height(r) <= 1
          let nr = mk(lrr, x, r)
          proof_assert fset_eq(
            elements(nr),
            fset_add(x, fset_union(elements(lrr), elements(r))),
          )
          proof_assert height(nr) == 1 + max2(height(lrr), height(r))
          proof_assert all_lt(elements(nl), lrx) && all_gt(lrx, elements(nr))
          proof_assert -1 <= height(nl) - height(nr) &&
            height(nl) - height(nr) <= 1
          proof_assert fset_eq(
            fset_add(lrx, fset_union(elements(nl), elements(nr))),
            fset_add(x, fset_union(elements(l), elements(r))),
          )
          mk(nl, lrx, nr)
        }
      }
  }
}

///|
#requires(balance_pre(l, x, r))
#requires(right_heavy(l, r))
#requires(right_double_case(r))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_right_double(l : Tree, x : Int, r : Tree) -> Tree {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) =>
      match rl {
        Empty => panic()
        Node(rll, rlx, rlr, _) => {
          proof_assert fset_mem(rlx, elements(r))
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
          proof_assert fset_eq(
            elements(nl),
            fset_add(x, fset_union(elements(l), elements(rll))),
          )
          proof_assert elements_subset(rlr, rl)
          proof_assert -1 <= height(rlr) - height(rr) &&
            height(rlr) - height(rr) <= 1
          proof_assert all_lt(elements(rlr), rx) && all_gt(rx, elements(rr))
          let nr = mk(rlr, rx, rr)
          proof_assert fset_eq(
            elements(nr),
            fset_add(rx, fset_union(elements(rlr), elements(rr))),
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
          proof_assert fset_eq(
            fset_add(rlx, fset_union(elements(nl), elements(nr))),
            fset_add(x, fset_union(elements(l), elements(r))),
          )
          mk(nl, rlx, nr)
        }
      }
  }
}

///|
#requires(balance_pre(l, x, r))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_exact_ok(l, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance(l : Tree, x : Int, r : Tree) -> Tree {
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
          proof_assert fset_eq(
            fset_add(lx, fset_union(elements(ll), elements(nr))),
            fset_add(x, fset_union(elements(l), elements(r))),
          )
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
#proof_decrease(t)
#requires(avl(t))
#requires(non_empty(t))
#ensures(remove_min_ok(t, result))
fn remove_min(t : Tree) -> (Int, Tree) {
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
          proof_assert all_gt(m, fset_union(elements(l1), elements(r)))
          proof_assert all_gt(m, elements(t1))
          proof_assert fset_eq(elements(t), fset_add(m, elements(t1)))
          proof_assert elements_subset(t1, t)
          (m, t1)
        }
      }
  }
}

///|
#proof_decrease(t)
#requires(avl(t))
#ensures(avl(result))
#ensures(insert_elements_ok(x, t, result))
#ensures(insert_height_lower_ok(t, result))
#ensures(insert_height_upper_ok(t, result))
pub fn insert(x : Int, t : Tree) -> Tree {
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
#proof_decrease(t)
#requires(avl(t))
#ensures(avl(result))
#ensures(delete_elements_ok(x, t, result))
#ensures(delete_height_lower_ok(t, result))
#ensures(delete_height_upper_ok(t, result))
pub fn delete(x : Int, t : Tree) -> Tree {
  match t {
    Empty => {
      proof_assert delete_elements_ok(x, t, Empty)
      Empty
    }
    Node(l, y, r, _) =>
      if x < y {
        let l1 = delete(x, l)
        proof_assert balance_pre(l1, y, r)
        let t1 = balance(l1, y, r)
        proof_assert fset_eq(
          elements(t1),
          fset_add(y, fset_union(fset_remove(x, elements(l)), elements(r))),
        )
        proof_assert delete_elements_ok(x, t, t1)
        t1
      } else if y < x {
        let r1 = delete(x, r)
        proof_assert balance_pre(l, y, r1)
        let t1 = balance(l, y, r1)
        proof_assert fset_eq(
          elements(t1),
          fset_add(y, fset_union(elements(l), fset_remove(x, elements(r)))),
        )
        proof_assert delete_elements_ok(x, t, t1)
        t1
      } else {
        match r {
          Empty => {
            proof_assert delete_elements_ok(x, t, l)
            l
          }
          Node(_, _, _, _) => {
            let (s, r1) = remove_min(r)
            proof_assert y < s
            proof_assert all_lt(elements(l), s)
            proof_assert balance_pre(l, s, r1)
            let t1 = balance(l, s, r1)
            proof_assert delete_elements_ok(x, t, t1)
            t1
          }
        }
      }
  }
}
