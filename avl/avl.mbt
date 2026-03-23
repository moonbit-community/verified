///|
priv enum Tree {
  Empty
  Node(Tree, Int, Tree, Int)
}

///|
#proof_external("set.Fset", "fset")
type Fset[T]

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
fn empty() -> Tree {
  Empty
}

///|
#requires(avl(l))
#requires(avl(r))
#requires(ordered_node(l, x, r))
#requires(balanced_heights(l, r))
#ensures(mk_ok(l, x, r, result))
fn mk(l : Tree, x : Int, r : Tree) -> Tree {
  let result = Node(l, x, r, 1 + max2(height(l), height(r)))
  proof_assert mk_ok(l, x, r, result)
  result
}

///|
fn contains(x : Int, t : Tree) -> Bool {
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
#requires(left_single_case(l))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_left_single(l : Tree, x : Int, r : Tree) -> Tree {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) =>
      if height(l) > height(r) + 1 {
        if height(ll) >= height(lr) {
          proof_assert lx < x
          proof_assert all_gt(lx, elements(r))
          proof_assert -1 <= height(lr) - height(r) && height(lr) - height(r) <= 1
          let nr = mk(lr, x, r)
          proof_assert fset_eq(elements(nr), fset_add(x, fset_union(elements(lr), elements(r))))
          proof_assert height(nr) == 1 + max2(height(lr), height(r))
          proof_assert -1 <= height(ll) - height(nr) && height(ll) - height(nr) <= 1
          proof_assert single_rotation_eq(x, lx, elements(ll), elements(lr), elements(r))
          proof_assert fset_eq(
            fset_add(lx, fset_union(elements(ll), elements(nr))),
            fset_add(x, fset_union(elements(l), elements(r))),
          )
          mk(ll, lx, nr)
        } else {
          panic()
        }
      } else {
        panic()
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
        Node(lrl, lrx, lrr, _) =>
          if height(l) > height(r) + 1 {
            if height(ll) < height(lr) {
              proof_assert fset_mem(lrx, elements(l))
              proof_assert lx < lrx
              proof_assert lrx < x
              proof_assert all_lt(elements(ll), lrx)
              proof_assert all_gt(lrx, elements(r))
              proof_assert -1 <= height(ll) - height(lrl) && height(ll) - height(lrl) <= 1
              proof_assert elements_subset(lrl, lr)
              proof_assert all_gt(lx, elements(lrl))
              proof_assert ordered_node(ll, lx, lrl)
              let nl = mk(ll, lx, lrl)
              proof_assert fset_eq(elements(nl), fset_add(lx, fset_union(elements(ll), elements(lrl))))
              proof_assert height(nl) == 1 + max2(height(ll), height(lrl))
              proof_assert elements_subset(lrr, lr)
              proof_assert all_lt(elements(lrr), x)
              proof_assert -1 <= height(lrr) - height(r) && height(lrr) - height(r) <= 1
              proof_assert ordered_node(lrr, x, r)
              let nr = mk(lrr, x, r)
              proof_assert fset_eq(elements(nr), fset_add(x, fset_union(elements(lrr), elements(r))))
              proof_assert height(nr) == 1 + max2(height(lrr), height(r))
              proof_assert all_lt(elements(nl), lrx)
              proof_assert all_gt(lrx, elements(nr))
              proof_assert ordered_node(nl, lrx, nr)
              proof_assert -1 <= height(nl) - height(nr) && height(nl) - height(nr) <= 1
              proof_assert fset_eq(
                fset_add(lrx, fset_union(elements(nl), elements(nr))),
                fset_add(x, fset_union(elements(l), elements(r))),
              )
              mk(nl, lrx, nr)
            } else {
              panic()
            }
          } else {
            panic()
          }
      }
  }
}

///|
#requires(balance_pre(l, x, r))
#requires(left_heavy(l, r))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_left(l : Tree, x : Int, r : Tree) -> Tree {
  match l {
    Empty => panic()
    Node(ll, _, lr, _) =>
      if height(ll) >= height(lr) {
        balance_left_single(l, x, r)
      } else {
        balance_left_double(l, x, r)
      }
  }
}

///|
#requires(balance_pre(l, x, r))
#requires(right_heavy(l, r))
#requires(right_single_case(r))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_right_single(l : Tree, x : Int, r : Tree) -> Tree {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) =>
      if height(r) > height(l) + 1 {
        if height(rr) >= height(rl) {
          proof_assert x < rx
          proof_assert all_lt(elements(l), rx)
          proof_assert -1 <= height(l) - height(rl) && height(l) - height(rl) <= 1
          let nl = mk(l, x, rl)
          proof_assert fset_eq(elements(nl), fset_add(x, fset_union(elements(l), elements(rl))))
          proof_assert height(nl) == 1 + max2(height(l), height(rl))
          proof_assert -1 <= height(nl) - height(rr) && height(nl) - height(rr) <= 1
          proof_assert single_rotation_eq(x, rx, elements(l), elements(rl), elements(rr))
          mk(nl, rx, rr)
        } else {
          panic()
        }
      } else {
        panic()
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
      if height(r) > height(l) + 1 {
        if height(rr) >= height(rl) {
          panic()
        } else {
          match rl {
            Empty => panic()
            Node(rll, rlx, rlr, _) => {
              proof_assert fset_mem(rlx, elements(r))
              proof_assert elements_subset(rl, r)
              proof_assert x < rlx
              proof_assert rlx < rx
              proof_assert all_lt(elements(l), rlx)
              proof_assert all_gt(rlx, elements(rr))
              proof_assert all_gt(x, elements(r))
              proof_assert all_gt(x, elements(rl))
              proof_assert all_gt(x, elements(rll))
              proof_assert -1 <= height(l) - height(rll) && height(l) - height(rll) <= 1
              let nl = mk(l, x, rll)
              proof_assert fset_eq(elements(nl), fset_add(x, fset_union(elements(l), elements(rll))))
              proof_assert elements_subset(rlr, rl)
              proof_assert all_lt(elements(rlr), rx)
              proof_assert -1 <= height(rlr) - height(rr) && height(rlr) - height(rr) <= 1
              let nr = mk(rlr, rx, rr)
              proof_assert fset_eq(elements(nr), fset_add(rx, fset_union(elements(rlr), elements(rr))))
              proof_assert all_lt(elements(nl), rlx)
              proof_assert all_gt(rlx, elements(nr))
              proof_assert ordered_node(nl, rlx, nr)
              proof_assert -1 <= height(nl) - height(nr) && height(nl) - height(nr) <= 1
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
      } else {
        panic()
      }
  }
}

///|
#requires(balance_pre(l, x, r))
#requires(right_heavy(l, r))
#ensures(avl(result))
#ensures(balance_elements_ok(l, x, r, result))
#ensures(balance_height_upper_ok(l, r, result))
#ensures(balance_height_lower_ok(l, r, result))
fn balance_right(l : Tree, x : Int, r : Tree) -> Tree {
  match r {
    Empty => panic()
    Node(rl, _, rr, _) =>
      if height(rr) >= height(rl) {
        balance_right_single(l, x, r)
      } else {
        balance_right_double(l, x, r)
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
       let result = balance_left(l, x, r)
        proof_assert avl(result)
        proof_assert balance_elements_ok(l, x, r, result)
        proof_assert balance_height_exact_ok(l, r, result)
        proof_assert balance_height_upper_ok(l, r, result)
        proof_assert balance_height_lower_ok(l, r, result)
        result
  } else if height(r) > height(l) + 1 {
    proof_assert right_heavy(l, r)
          let result = balance_right(l, x, r)
           proof_assert avl(result)
             proof_assert balance_elements_ok(l, x, r, result)
             proof_assert balance_height_exact_ok(l, r, result)
             proof_assert balance_height_upper_ok(l, r, result)
            proof_assert balance_height_lower_ok(l, r, result)
           result
  } else {
    proof_assert balanced_heights(l, r)
          let result = mk(l, x, r)
           proof_assert avl(result)
              proof_assert balance_elements_ok(l, x, r, result)
              proof_assert balance_height_exact_ok(l, r, result)
             proof_assert balance_height_upper_ok(l, r, result)
            proof_assert balance_height_lower_ok(l, r, result)
           result
  }
}

///|
#proof_decrease(t)
#requires(avl(t))
#ensures(avl(result))
#ensures(insert_elements_ok(x, t, result))
#ensures(insert_height_lower_ok(t, result))
#ensures(insert_height_upper_ok(t, result))
fn insert(x : Int, t : Tree) -> Tree {
  match t {
    Empty => mk(Empty, x, Empty)
    Node(l, y, r, _) =>
        if x < y {
          let l1 = insert(x, l)
          proof_assert fset_eq(
            fset_add(y, fset_union(elements(l1), elements(r))),
            fset_add(x, fset_add(y, fset_union(elements(l), elements(r)))),
          )
          proof_assert balance_pre(l1, y, r)
          let result = balance(l1, y, r)
          proof_assert avl(result)
          proof_assert insert_elements_ok(x, t, result)
          proof_assert stored_height_ok(l, r, height(t))
          proof_assert height(l) <= height(l1)
          proof_assert height(l1) <= height(l) + 1
          proof_assert balance_height_lower_ok(l1, r, result)
          proof_assert balance_height_exact_ok(l1, r, result)
          proof_assert balance_height_upper_ok(l1, r, result)
          if height(l1) > height(r) + 1 {
            proof_assert height(t) <= height(result)
          } else {
            proof_assert balanced_heights(l1, r)
            proof_assert height(result) == 1 + max2(height(l1), height(r))
            proof_assert height(t) <= height(result)
          }
          proof_assert height(result) <= height(t) + 1
          result
        } else if y < x {
          let r1 = insert(x, r)
          proof_assert fset_eq(
            fset_add(y, fset_union(elements(l), elements(r1))),
            fset_add(x, fset_add(y, fset_union(elements(l), elements(r)))),
          )
          proof_assert balance_pre(l, y, r1)
          let result = balance(l, y, r1)
          proof_assert avl(result)
          proof_assert insert_elements_ok(x, t, result)
          proof_assert stored_height_ok(l, r, height(t))
          proof_assert height(r) <= height(r1)
          proof_assert height(r1) <= height(r) + 1
          proof_assert balance_height_lower_ok(l, r1, result)
          proof_assert balance_height_exact_ok(l, r1, result)
          proof_assert balance_height_upper_ok(l, r1, result)
          if height(r1) > height(l) + 1 {
            proof_assert height(t) <= height(result)
          } else {
            proof_assert balanced_heights(l, r1)
            proof_assert height(result) == 1 + max2(height(l), height(r1))
            proof_assert height(t) <= height(result)
          }
          proof_assert height(result) <= height(t) + 1
          result
        } else {
          t
        }
  }
}
