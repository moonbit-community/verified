///|
using @seq {type Seq}

///|
let num_bits = 5

///|
let branching_factor : Int = 1 << num_bits

///|
let bitmask : Int = branching_factor - 1

///|
const LINEAR_THRESHOLD : Int = 4

///|
pub struct Vector[T] {
  tree : Tree[T]
  tail : ReadOnlyArray[T]
  size : Int
  shift : Int
}

///|
enum Tree[T] {
  Empty
  Node(ReadOnlyArray[Tree[T]], ReadOnlyArray[Int]?)
  Leaf(ReadOnlyArray[T])
}
