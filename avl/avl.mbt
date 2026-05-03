///|
using @fset {type Fset}

///|
pub enum Tree[T] {
  Empty
  Node(Tree[T], T, Tree[T], Int)
}

///|
#proof_pure
fn[T] height(t : Tree[T]) -> Int {
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
pub fn[T] empty() -> Tree[T] {
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
fn[T : Compare] mk(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: mk_pre(l, x, r),
  proof_ensure: result => mk_post(l, x, r, result),
} {
  Node(l, x, r, 1 + max2(height(l), height(r)))
}

///|
pub fn[T : Compare] contains(x : T, t : Tree[T]) -> Bool {
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
fn[T : Compare] balance_left_double(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: left_double_pre(l, x, r),
  proof_ensure: result => rebalance_post(l, x, r, result),
} {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) =>
      match lr {
        Empty => panic()
        Node(lrl, lrx, lrr, _) => {
          let nl = mk(ll, lx, lrl)
          let nr = mk(lrr, x, r)
          proof_assert all_lt(nl.model(), lrx)
          proof_assert all_gt(lrx, nr.model())
          proof_assert nl
            .model()
            .union(nr.model())
            .add(lrx)
            .eq(l.model().union(r.model()).add(x))
          let result = mk(nl, lrx, nr)
          proof_assert rebalance_post(l, x, r, result)
          result
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
fn[T : Compare] balance_right_double(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: right_double_pre(l, x, r),
  proof_ensure: result => rebalance_post(l, x, r, result),
} {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) =>
      match rl {
        Empty => panic()
        Node(rll, rlx, rlr, _) => {
          proof_assert x < rlx
          proof_assert rlx < rx
          proof_assert all_lt(l.model(), rlx)
          proof_assert all_gt(rlx, rr.model())
          let nl = mk(l, x, rll)
          let nr = mk(rlr, rx, rr)
          proof_assert all_lt(nl.model(), rlx)
          proof_assert all_gt(rlx, nr.model())
          proof_assert nl
            .model()
            .union(nr.model())
            .add(rlx)
            .eq(l.model().union(r.model()).add(x))
          let result = mk(nl, rlx, nr)
          proof_assert rebalance_post(l, x, r, result)
          result
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
fn[T : Compare] balance_left_single(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: left_single_pre(l, x, r),
  proof_ensure: result => rebalance_post(l, x, r, result),
} {
  match l {
    Empty => panic()
    Node(ll, lx, lr, _) => {
      let nr = mk(lr, x, r)
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
fn[T : Compare] balance_right_single(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: right_single_pre(l, x, r),
  proof_ensure: result => rebalance_post(l, x, r, result),
} {
  match r {
    Empty => panic()
    Node(rl, rx, rr, _) => {
      let nl = mk(l, x, rl)
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
fn[T : Compare] balance(
  l : Tree[T],
  x : T,
  r : Tree[T],
) -> Tree[T] where {
  proof_require: balance_pre(l, x, r),
  proof_ensure: result => rebalance_post(l, x, r, result),
  proof_ensure: result => {
    !balanced_heights(l, r) || height(result) == 1 + max2(height(l), height(r))
  },
} {
  if height(l) > height(r) + 1 {
    match l {
      Empty => panic()
      Node(ll, _lx, lr, _) =>
        if height(ll) >= height(lr) {
          balance_left_single(l, x, r)
        } else {
          balance_left_double(l, x, r)
        }
    }
  } else if height(r) > height(l) + 1 {
    match r {
      Empty => panic()
      Node(rl, _rx, rr, _) =>
        if height(rr) >= height(rl) {
          balance_right_single(l, x, r)
        } else {
          balance_right_double(l, x, r)
        }
    }
  } else {
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
fn[T : Compare] remove_min(
  t : Tree[T],
) -> (T, Tree[T]) where {
  proof_decrease: t,
  proof_require: remove_min_pre(t),
  proof_ensure: result => remove_min_post(t, result),
} {
  match t {
    Empty => panic()
    Node(l, y, r, _) =>
      match l {
        Empty => {
          let result = (y, r)
          proof_assert remove_min_post(t, result)
          result
        }
        Node(_, _, _, _) => {
          let (m, l1) = remove_min(l)
          proof_assert l.model().eq(l1.model().add(m))
          proof_assert balance_pre(l1, y, r)
          let t1 = balance(l1, y, r)
          let result = (m, t1)
          proof_assert remove_min_post(t, result)
          result
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
pub fn[T : Compare] insert(
  x : T,
  t : Tree[T],
) -> Tree[T] where {
  proof_decrease: t,
  proof_require: avl_inv(t),
  proof_ensure: result => insert_post(x, t, result),
} {
  match t {
    Empty => mk(Empty, x, Empty)
    Node(l, y, r, _) =>
      if x < y {
        let l1 = insert(x, l)
        proof_assert all_lt(l1.model(), y)
        proof_assert balance_pre(l1, y, r)
        let t1 = balance(l1, y, r)
        proof_assert insert_post(x, t, t1)
        t1
      } else if y < x {
        let r1 = insert(x, r)
        proof_assert all_gt(y, r1.model())
        proof_assert balance_pre(l, y, r1)
        let t1 = balance(l, y, r1)
        proof_assert insert_post(x, t, t1)
        t1
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
pub fn[T : Compare] delete(
  x : T,
  t : Tree[T],
) -> Tree[T] where {
  proof_decrease: t,
  proof_require: avl_inv(t),
  proof_ensure: result => delete_post(x, t, result),
} {
  match t {
    Empty => Empty
    Node(l, y, r, _) =>
      if x < y {
        let l1 = delete(x, l)
        proof_assert balance_pre(l1, y, r)
        let t1 = balance(l1, y, r)
        proof_assert delete_post(x, t, t1)
        t1
      } else if y < x {
        let r1 = delete(x, r)
        proof_assert balance_pre(l, y, r1)
        let t1 = balance(l, y, r1)
        proof_assert delete_post(x, t, t1)
        t1
      } else {
        proof_assert x == y
        match r {
          Empty => {
            proof_assert delete_post(x, t, l)
            l
          }
          Node(_, _, _, _) => {
            let (s, r1) = remove_min(r)
            proof_assert r.model().eq(r1.model().add(s))
            proof_assert balance_pre(l, s, r1)
            let t1 = balance(l, s, r1)
            proof_assert delete_post(x, t, t1)
            t1
          }
        }
      }
  }
}
