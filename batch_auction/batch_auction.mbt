///|
pub struct AuctionResult {
  quantity : Int
  price : Int
} derive(Eq)

///|
pub fn clearing_quantity(
  bids : FixedArray[Int],
  asks : FixedArray[Int],
) -> Int where {
  proof_require: same_length(bids, asks),
  proof_require: bids_desc(bids),
  proof_require: asks_asc(asks),
  proof_ensure: result => clearing_quantity_post(bids, asks, result),
} {
  for lo = 0, hi = bids.length(); lo < hi; {
    let mid = lo + (hi - lo) / 2
    if asks[mid] <= bids[mid] {
      continue mid + 1, hi
    } else {
      continue lo, mid
    }
  } nobreak {
    lo
  } where {
    proof_invariant: 0 <= lo,
    proof_invariant: lo <= hi,
    proof_invariant: hi <= bids.length(),
    proof_invariant: all_cross_before(bids, asks, lo),
    proof_invariant: all_fail_from(bids, asks, hi),
    proof_reasoning: (
      #| The search window `[lo, hi)` brackets the frontier between executable
      #| matches and non-crossing quotes.
      #|
      #| Every index before `lo` is already known to satisfy `ask <= bid`, while
      #| every index from `hi` onward is already known to fail that crossing
      #| condition.
      #|
      #| Monotonicity comes from the order-book assumptions: bids are sorted
      #| descending and asks are sorted ascending. So if a midpoint crosses,
      #| every earlier price level also crosses; if a midpoint fails, every
      #| later level fails as well.
      #|
      #| The measure `hi - lo` strictly decreases because integer division gives
      #| `lo <= mid < hi`, so both `lo := mid + 1` and `hi := mid` shrink the
      #| window.
      #|
      #| When the loop ends, `lo == hi`, and the two quantified invariants meet
      #| at the exact clearing quantity.
    ),
  }
}

///|
pub fn clear_book(
  bids : FixedArray[Int],
  asks : FixedArray[Int],
) -> AuctionResult where {
  proof_require: same_length(bids, asks),
  proof_require: bids_desc(bids),
  proof_require: asks_asc(asks),
  proof_ensure: result => auction_result_post(bids, asks, result),
} {
  let quantity = clearing_quantity(bids, asks)
  let price = if quantity == 0 {
    0
  } else {
    asks[quantity - 1] + (bids[quantity - 1] - asks[quantity - 1]) / 2
  }
  let result = { quantity, price }
  proof_assert auction_result_post(bids, asks, result)
  result
}
