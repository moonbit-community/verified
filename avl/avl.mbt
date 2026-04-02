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
/// Canonical node construction for the AVL invariant.
///
/// The proof obligations here are the spine of the whole file:
/// `l` and `r` must already be valid AVL trees, every key in `l` must stay
/// below `x`, every key in `r` must stay above `x`, and the heights must be
/// close enough that the new node can be formed without rebalancing. The
/// returned height is computed directly from the children, so later proofs can
/// treat `mk` as the single place where structure, ordering, and height are
/// recombined.
fn mk(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: avl_inv(l),
  proof_require: avl_inv(r),
  proof_require: all_lt(l.model(), x),
  proof_require: all_gt(x, r.model()),
  proof_require: balanced_heights(l, r),
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => {
    result.model().eq(l.model().union(r.model()).add(x))
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
/// Double rotation on a left-heavy tree when the left child is right-heavy.
///
/// The proof split matches the standard AVL case analysis: first expose the
/// left child, then the left-right grandchild, and use the stored ordering and
/// height facts to rebuild two balanced subtrees before the final root rebuild.
/// The intermediate `mk` calls isolate the local rotations; the final equality
/// proof shows that the rotated tree preserves exactly the same element set as
/// the pre-rotation configuration.
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
          proof_assert l.model().mem(lrx)
          proof_assert lx < lrx
          proof_assert lrx < x
          proof_assert all_gt(lrx, r.model())
          proof_assert elements_subset(lr, l)
          proof_assert all_lt(lr.model(), x)
          proof_assert -1 <= height(ll) - height(lrl) &&
            height(ll) - height(lrl) <= 1
          proof_assert elements_subset(lrl, lr)
          proof_assert all_gt(lx, lrl.model())
          proof_assert all_lt(ll.model(), lx) && all_gt(lx, lrl.model())
          let nl = mk(ll, lx, lrl)
          proof_assert nl.model().eq(
            ll.model().union(lrl.model()).add(lx),
          )
          proof_assert height(nl) == 1 + max2(height(ll), height(lrl))
          proof_assert elements_subset(lrr, lr)
          proof_assert all_lt(lrr.model(), x)
          proof_assert all_gt(x, r.model())
          proof_assert -1 <= height(lrr) - height(r) &&
            height(lrr) - height(r) <= 1
          let nr = mk(lrr, x, r)
          proof_assert nr.model().eq(lrr.model().union(r.model()).add(x))
          proof_assert height(nr) == 1 + max2(height(lrr), height(r))
          proof_assert all_lt(nl.model(), lrx) && all_gt(lrx, nr.model())
          proof_assert -1 <= height(nl) - height(nr) &&
            height(nl) - height(nr) <= 1
          proof_assert nl
            .model()
            .union(nr.model())
            .add(lrx)
            .eq(l.model().union(r.model()).add(x))
          mk(nl, lrx, nr)
        }
      }
  }
}

///|
/// Double rotation on a right-heavy tree when the right child is left-heavy.
///
/// This is the mirror image of the left-double case. The proof discharges the
/// same three obligations in mirrored order: preserve the in-order partition,
/// rebuild balanced children around the inner grandchild, and then show the
/// final tree keeps both the AVL height bound and the exact element set.
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
          proof_assert r.model().mem(rlx)
          proof_assert elements_subset(rl, r)
          proof_assert elements_subset(rll, rl)
          proof_assert x < rlx
          proof_assert rlx < rx
          proof_assert all_lt(l.model(), rlx)
          proof_assert all_gt(rlx, rr.model())
          proof_assert -1 <= height(l) - height(rll) &&
            height(l) - height(rll) <= 1
          proof_assert all_gt(x, rl.model())
          proof_assert all_lt(l.model(), x) && all_gt(x, rll.model())
          let nl = mk(l, x, rll)
          proof_assert nl.model().eq(l.model().union(rll.model()).add(x))
          proof_assert elements_subset(rlr, rl)
          proof_assert -1 <= height(rlr) - height(rr) &&
            height(rlr) - height(rr) <= 1
          proof_assert all_lt(rlr.model(), rx) && all_gt(rx, rr.model())
          let nr = mk(rlr, rx, rr)
          proof_assert nr.model().eq(
            rlr.model().union(rr.model()).add(rx),
          )
          proof_assert all_lt(nl.model(), rlx) && all_gt(rlx, nr.model())
          proof_assert -1 <= height(nl) - height(nr) &&
            height(nl) - height(nr) <= 1
          proof_assert double_rotation_eq_rl(
            x,
            rlx,
            rx,
            l.model(),
            rll.model(),
            rlr.model(),
            rr.model(),
          )
          proof_assert nl
            .model()
            .union(nr.model())
            .add(rlx)
            .eq(l.model().union(r.model()).add(x))
          mk(nl, rlx, nr)
        }
      }
  }
}

///|
/// Single rotation for the left-heavy but not left-double case.
///
/// The non-double assumption tells us the left child's right subtree is not
/// taller than its left subtree, so one rotation is enough. The proof first
/// rebuilds the right subtree around `x`, then uses the cached height relation
/// to show the new root is balanced and preserves exactly the same set of
/// elements as the unrebalanced node.
fn balance_left_single(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: balance_pre(l, x, r),
  proof_require: left_heavy(l, r),
  proof_require: left_double_case(l) == false,
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => balance_elements_post(l, x, r, result),
  proof_ensure: result => balance_height_upper_post(l, r, result),
  proof_ensure: result => balance_height_lower_post(l, r, result),
} {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) => {
      proof_assert l.model().eq(ll.model().union(lr.model()).add(lx))
      proof_assert lx < x
      proof_assert all_gt(lx, r.model())
      proof_assert elements_subset(lr, l)
      proof_assert all_lt(lr.model(), x)
      proof_assert -1 <= height(lr) - height(r) &&
        height(lr) - height(r) <= 1
      proof_assert all_lt(lr.model(), x) && all_gt(x, r.model())
      let nr = mk(lr, x, r)
      proof_assert nr.model().eq(lr.model().union(r.model()).add(x))
      proof_assert -1 <= height(ll) - height(nr) &&
        height(ll) - height(nr) <= 1
      proof_assert single_rotation_eq(
        lx,
        x,
        ll.model(),
        lr.model(),
        r.model(),
      )
      proof_assert ll
        .model()
        .union(nr.model())
        .add(lx)
        .eq(l.model().union(r.model()).add(x))
      mk(ll, lx, nr)
    }
  }
}

///|
/// Single rotation for the right-heavy but not right-double case.
///
/// This is the symmetric one-rotation repair. The proof structure is the same
/// as the left-single case, but with the subtrees swapped: rebuild the left
/// child around `x`, use the height inequality to justify the new root, and
/// finish by rewriting the element-set equation back to the original tree.
fn balance_right_single(
  l : Tree,
  x : Int,
  r : Tree,
) -> Tree where {
  proof_require: balance_pre(l, x, r),
  proof_require: right_heavy(l, r),
  proof_require: right_double_case(r) == false,
  proof_ensure: result => avl_inv(result),
  proof_ensure: result => balance_elements_post(l, x, r, result),
  proof_ensure: result => balance_height_upper_post(l, r, result),
  proof_ensure: result => balance_height_lower_post(l, r, result),
} {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) => {
      proof_assert r.model().eq(rl.model().union(rr.model()).add(rx))
      proof_assert x < rx
      proof_assert all_lt(l.model(), rx)
      proof_assert elements_subset(rl, r)
      proof_assert all_gt(x, rl.model())
      proof_assert -1 <= height(l) - height(rl) &&
        height(l) - height(rl) <= 1
      proof_assert all_lt(l.model(), x) && all_gt(x, rl.model())
      let nl = mk(l, x, rl)
      proof_assert nl.model().eq(l.model().union(rl.model()).add(x))
      proof_assert -1 <= height(nl) - height(rr) &&
        height(nl) - height(rr) <= 1
      proof_assert single_rotation_eq(
        x,
        rx,
        l.model(),
        rl.model(),
        rr.model(),
      )
      proof_assert nl
        .model()
        .union(rr.model())
        .add(rx)
        .eq(l.model().union(r.model()).add(x))
      mk(nl, rx, rr)
    }
  }
}

///|
/// Rebalance a node after a child update.
///
/// The proof is a case split on the relative heights of `l` and `r`. If one
/// side is too tall, we inspect the heavier child to decide between the single
/// and double rotation lemmas; otherwise `mk` is already sufficient. This
/// function is the bridge between recursive edits and the local AVL repair
/// lemmas above.
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
      Node(ll, _lx, lr, _) =>
        if height(ll) >= height(lr) {
          proof_assert left_double_case(l) == false
          balance_left_single(l, x, r)
        } else {
          proof_assert left_double_case(l)
          balance_left_double(l, x, r)
        }
    }
  } else if height(r) > height(l) + 1 {
    proof_assert right_heavy(l, r)
    match r {
      Empty => panic()
      Node(rl, _rx, rr, _) =>
        if height(rr) >= height(rl) {
          proof_assert right_double_case(r) == false
          balance_right_single(l, x, r)
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
/// Remove and return the minimum element from a non-empty AVL tree.
///
/// The proof decreases on the tree shape. When the left child is empty, the
/// root is already the minimum and the right subtree is returned unchanged.
/// Otherwise the recursive call removes the minimum from the left branch, and
/// the remaining proof work shows that balancing the modified left subtree with
/// the original root preserves both the AVL invariant and the set of
/// elements minus that minimum.
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
          proof_assert remove_min_post(l, (m, l1))
          proof_assert avl_inv(l1)
          proof_assert l.model().mem(m)
          proof_assert l.model().eq(l1.model().add(m))
          proof_assert elements_subset(l1, l)
          proof_assert all_gt(m, l1.model())
          proof_assert elements_subset(l, t)
          proof_assert elements_subset(l1, t)
          proof_assert m < y
          proof_assert all_gt(m, r.model())
          proof_assert balance_pre(l1, y, r)
          let t1 = balance(l1, y, r)
          proof_assert all_gt(m, l1.model().union(r.model()))
          proof_assert all_gt(m, t1.model())
          proof_assert height(l1) <= height(l)
          proof_assert height(l) <= height(l1) + 1
          proof_assert height(t1) <= height(t)
          proof_assert height(t) <= height(t1) + 1
          proof_assert t.model().eq(t1.model().add(m))
          proof_assert elements_subset(t1, t)
          proof_assert remove_min_post(t, (m, t1))
          (m, t1)
        }
      }
  }
}

///|
/// Insert by descending to the unique ordered position, then rebalance on the
/// way back up.
///
/// The recursive proof mirrors the algorithm: recurse into the left or right
/// subtree depending on the comparison, prove the updated child still satisfies
/// `balance_pre`, and let `balance` restore the local invariant. The equal case
/// is the no-op branch, so the tree is returned unchanged.
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
/// Delete by ordered search, with a successor replacement when the node has
/// two children.
///
/// The proof follows the same structural recursion as insertion, but the equal
/// case needs a split: if the right child is empty, the left subtree already is
/// the correct result; otherwise `remove_min` supplies the successor `s` and the
/// remaining right subtree, after which `balance` restores AVL shape around the
/// replacement root.
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
        proof_assert t1.model().eq(
          l.model().remove(x).union(r.model()).add(y),
        )
        proof_assert delete_elements_post(x, t, t1)
        t1
      } else if y < x {
        let r1 = delete(x, r)
        proof_assert balance_pre(l, y, r1)
        let t1 = balance(l, y, r1)
        proof_assert t1.model().eq(
          l.model().union(r.model().remove(x)).add(y),
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
            proof_assert all_lt(l.model(), s)
            proof_assert balance_pre(l, s, r1)
            let t1 = balance(l, s, r1)
            proof_assert delete_elements_post(x, t, t1)
            t1
          }
        }
      }
  }
}
