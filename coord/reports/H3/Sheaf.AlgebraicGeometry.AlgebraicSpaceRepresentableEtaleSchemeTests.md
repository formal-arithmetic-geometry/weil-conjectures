## What changed

Completed all ten conjuncts of
`AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`.
The public theorem statement is unchanged. Two fully proved private bridge lemmas
identify the project's scheme-test predicates with Mathlib's relative representability
and relative morphism properties. Two private instances transport scheme étale and
surjective base-change stability to schemes over S. Mathlib supplies the diagonal,
composition, isomorphism, base-change, and Yoneda-map arguments. The comparison clause
uses the graph section and scheme étale cancellation, as planned.

Updated only proof, proof_deps and proof_origin of
`lem-trf-space-representable-etale-scheme-tests` to match this proof.
The change record is
`coord/changes/h3-representable-etale-scheme-tests-import-pruning.md`.
No consumer adaptation or definition change is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests`
(node `lem-trf-space-representable-etale-scheme-tests`).
Validation: the final module compiled with no errors or warnings. The theorem's
`#print axioms` output is exactly `propext`, `Classical.choice`, and `Quot.sound`.
All ten conjuncts are proved; zero sorry remain in the item and zero are added
elsewhere. This is a proof, not a decomposition. No new statements with holes,
new modules, or new nodes are introduced.

## No longer needed

Removed the public proof-plan import
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
the theorem only needs the underlying sheaf pullback square, whose image in presheaves
is a pullback. It never needs to bundle the resulting sheaf as an algebraic space.
This removes the item's dependency on `lem-trf-space-fibre-products-etale-covers`;
it does not withdraw that node or module, which other arguments still need.

Removed redundant private imports `Mathlib.CategoryTheory.Yoneda`,
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`, and
`Mathlib.CategoryTheory.Limits.MorphismProperty`.
Added private proof imports `Mathlib.CategoryTheory.MorphismProperty.Representable`,
`Mathlib.CategoryTheory.Limits.Yoneda`, and `Mathlib.AlgebraicGeometry.PullbackCarrier`.

Removed direct proof dependencies `def-weil-open-immersion`,
`lem-weil-pbc-etale-covering-composition`, and
`lem-weil-pbc-etale-covering-base-change`: generic morphism-property calculus uses
étale and surjective scheme properties directly, without covering families or a
separate open-immersion argument. Surjective composition is the existing Mathlib leaf
`lem-trf-surjective-morphism-composition`; surjective base change is the existing
Mathlib leaf `lem-weil-pbc-surjective-base-change`. No unit route is bypassed.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The theorem is correct, including empty schemes and non-surjective étale charts.
The original docstring and DAG plan invoke algebraic-space closure for the sheaf
pullback, but that is stronger than the Lean statement needs. The proof uses
preservation of sheaf pullbacks instead. The natural-language plan is otherwise
implemented through Mathlib's already proved relative-property API.

The unit record sk-i-curve-zero has no realized statements or steps attached to this
foundation node. Its unit statement and route have not been changed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
