///|
test "generated proof verifies" {
  let left = @merkle_tree.combine(
    @merkle_tree.singleton(10),
    @merkle_tree.singleton(20),
  )
  let right = @merkle_tree.combine(
    @merkle_tree.singleton(30),
    @merkle_tree.singleton(40),
  )
  let tree = @merkle_tree.combine(left, right)
  inspect(@merkle_tree.generated_proof_verifies(tree, 2), content="true")
  match @merkle_tree.make_proof(tree, 2) {
    Some(proof) =>
      inspect(
        @merkle_tree.verify_proof(30, proof, @merkle_tree.root(tree)),
        content="true",
      )
    None => fail("expected proof")
  }
}

///|
test "wrong leaf does not verify for simple hashes" {
  let tree = @merkle_tree.combine(
    @merkle_tree.combine(@merkle_tree.singleton(1), @merkle_tree.singleton(2)),
    @merkle_tree.singleton(3),
  )
  match @merkle_tree.make_proof(tree, 1) {
    Some(proof) =>
      inspect(
        @merkle_tree.verify_proof(99, proof, @merkle_tree.root(tree)),
        content="false",
      )
    None => fail("expected proof")
  }
}
