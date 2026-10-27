## What changed

Shortened the coefficient-map compatibility proof in
`AlgebraicGeometry.bertini_singular_fibre_polynomial_equations`: the manual constant/variable
extensionality calculation is replaced by `MvPolynomial.map_eq_eval₂Hom_C_comp`,
`MvPolynomial.comp_eval₂Hom`, and definitional equality. This removes eleven lines of
proof while retaining the actual coordinate ring, its scalar algebra structure, the
surjective quotient, the jet relations, and the coefficient projection equality.
The item's node describes this composition calculation. All signatures, definitions,
attributes, public imports, and proof dependencies are preserved.

Validation: the current repository version compiled in 5.7 seconds, and the shortened
proof compiled cleanly through `lcompile.py` in 4.0 seconds. The existing coordinate and
jet-tensor declarations were read against their node statements. The coordinate theorem
supplies the actual affine presentation; tensor contraction supplies every dual-functional
relation, and the final composition calculation supplies the original coefficient map.
No generation, immersion, residue-field closure, or jet-rank hypothesis is introduced.
Empty fibres, empty index types, zero sections, and zero cotangent rank require no cases.

Search: `msearch.py` Loogle found `TensorProduct.rid_tmul`; LeanFinder found
`MvPolynomial.ringHom_ext` and related extensionality lemmas. A local Mathlib search in
`Algebra/MvPolynomial/Eval.lean` found the two composition identities used here.
A library search confirmed that the theorem's existing parent is
`Sheaf.AlgebraicGeometry.BertiniSingularFibreEquations`.

## Proved and sorry left

Actual item hole count at the start: zero. Actual item hole count delivered: zero.
Holes closed: none (0 of 0). Holes added or split off: none.
`AlgebraicGeometry.bertini_singular_fibre_polynomial_equations` and its private helper
`polynomial_relation_of_jet_tensor` were already proved in the current source. Their
proofs remain complete. This delivery is an audited proof simplification, not a new
proof or a decomposition, and claims no net hole reduction.

## No longer needed

No imports, nodes, or modules are pruned. Both declared dependencies remain used:
`lem-zl-bertini-singular-fibre-coordinates` and
`lem-zl-bertini-singular-fibre-jet-tensor`. The manual constant/variable extensionality
calculation is superseded by Mathlib's polynomial composition identities.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief says this module contains a hole or an assigned repair. The current
source already has a complete proof landed by K2; its jet-tensor dependency also has a
complete proof landed by S1. No current repair, return, or rework record names the item.
The D2 claim exists, but the assignment is stale relative to the current source. This
report records that discrepancy instead of claiming to close an already closed hole.
No mathematical statement or unit route was found wrong. The prescribed Bertini input
and its parents are retained; nothing is withdrawn and no adopted source module changes.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
