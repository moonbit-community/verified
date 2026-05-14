///|
test "generated proof verifies" {
  let left = combine(singleton(10), singleton(20))
  let right = combine(singleton(30), singleton(40))
  let tree = combine(left, right)
  inspect(generated_proof_verifies(tree, 2), content="true")
  match make_proof(tree, 2) {
    Some(proof) => inspect(verify_proof(30, proof, root(tree)), content="true")
    None => fail("expected proof")
  }
}

///|
test "wrong leaf does not verify for simple hashes" {
  let tree = combine(combine(singleton(1), singleton(2)), singleton(3))
  match make_proof(tree, 1) {
    Some(proof) => inspect(verify_proof(99, proof, root(tree)), content="false")
    None => fail("expected proof")
  }
}
