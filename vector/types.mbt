///|
using @seq {type Seq}

///|
let num_bits = 5

///|
let branching_factor : Int32 = 1 << num_bits

///|
let bitmask : Int32 = branching_factor - 1

///|
const LINEAR_THRESHOLD : Int32 = 4

///|
pub struct Vector[T] {
  tree : Tree[T]
  tail : ReadOnlyArray[T]
  size : Int32
  shift : Int32
}

///|
enum Tree[T] {
  Empty
  Node(ReadOnlyArray[Tree[T]], ReadOnlyArray[Int32]?)
  Leaf(ReadOnlyArray[T])
}
