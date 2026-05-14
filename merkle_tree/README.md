# Verified Merkle Tree Core

This package contains a small verified Merkle tree core. It verifies the tree
and proof-path bookkeeping:

- trees built with `singleton` and `combine` satisfy the Merkle invariant;
- `make_proof(tree, index)` returns a membership path for the indexed leaf;
- `verify_proof(data, proof, root)` replays a path against a root hash;
- `generated_proof_verifies(tree, index)` states the end-to-end property that a
  generated proof verifies for the indexed leaf and the tree root.

The hash boundary is intentionally trusted in this first version. Leaves and
hashes are represented as `Int`, with toy hash functions connected to the proof
model by small `proof_axiomatized` wrappers. The package proves Merkle tree
bookkeeping, not cryptographic collision resistance or a concrete hash
implementation.

Raw hash-bearing nodes are private. Public trees should be constructed through
`singleton` and `combine`.
