# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-quasi-compact-local-on-target.json`: Mathlib leaf; no new nodes.

Attachments: none.

WANTED: none.

The item has no matching declaration in the slopmaster2 Lean source (the blueprint tag and the key phrases were searched).  Its statement is the standard target-locality criterion for quasi-compact morphisms.  The Mathlib declaration `HasAffineProperty @QuasiCompact` in `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:117` supplies the affine-local property, and the generic instance in `Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:588-609` supplies `IsZariskiLocalAtTarget @QuasiCompact`; the theorem at `Basic.lean:156-158` then gives the stated open-cover criterion.  I retained the item's statement and recorded this as a Mathlib leaf.  No proof steps or new nodes are needed, so `citations.json` is empty.

## Review by M1

I read the item node, its blueprint ancestor `lem-pc-degree-base-change`, and the Mathlib sources `Morphisms/QuasiCompact.lean` and `Morphisms/Basic.lean`.  The item hypotheses match the generic theorem: a morphism of schemes, an indexed family of open target subschemes whose supremum is the whole target, and quasi-compact restrictions.  `IsZariskiLocalAtTarget.iff_of_iSup_eq_top` states exactly that these restricted morphisms imply quasi-compactness of the original morphism; its restriction notation is the same open-subscheme morphism as `f^{-1}(Y_i) -> Y_i`.  The `HasAffineProperty @QuasiCompact` instance is the source of the required local-at-target instance, so no unquoted non-elementary proof fact remains.  I searched the complete DAG and imported blueprint for the item id, Tag 03KG, and the local-on-target wording; no duplicate node was found.  Small edge cases checked were a one-member cover (the theorem reduces to the original morphism) and the empty target cover (only possible for the empty target, where the implication is vacuous).  Since the node is a Mathlib leaf there are no proof-step citations; the empty citations list is intentional.
