///|
/// The map proof surface stays abstract as well, so key/domain lemmas can talk about the
/// abstract map behavior without committing to an encoding.
using @fset {type Fset}

///|
#proof_external("fmap.Fmap", "fmap")
pub type Fmap[K, V]
