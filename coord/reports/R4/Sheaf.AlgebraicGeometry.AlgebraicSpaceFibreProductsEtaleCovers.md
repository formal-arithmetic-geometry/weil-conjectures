## What changed

Filled all three theorem bodies in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` using the three
existing stated proof dependencies. Added private proved helpers for the pointwise
pullback universal property, the comparison with the chosen sheaf pullback, and
transport of scheme-test properties through isomorphisms. The diagonal theorem
and atlas-test theorem now give algebraic-space closure, while the categorical
pullback gives the unique lift. The point-lifting theorem gives the covering
clause and the scheme special case after the same comparison.

Existing public statements, definitions and public imports are unchanged. Updated
only the item's node proof and proof origin to describe these comparison maps.

Validation: the complete item compiles cleanly through `lcompile.py` in 6.6 s.
Import-direction checks accept all three added Sheaf proof imports. No shared
interface changed, so no consumer adaptation is required.

## Proved and sorry left

Closed 3 of the original 3 holes:

- `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`.
- `AlgebraicGeometry.AlgebraicSpace.etaleCover_pullback`.
- `AlgebraicGeometry.AlgebraicSpace.etale_fibreProduct_isScheme`.

All belong to `lem-trf-space-fibre-products-etale-covers`. No holes remain in the
item; no holes or split-off declarations are added. These are proofs from the
existing declared dependencies, not a claim that their transitive axioms are
already sorry-free. In particular, `sheafPullback_diagonal` in the existing
`Sheaf.AlgebraicGeometry.SheafPullbackDiagonal` still has its original hole.

## No longer needed

Removed the unused private imports `Mathlib.AlgebraicGeometry.PullbackCarrier`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, and
`Sheaf.CategoryTheory.SiteCoveringAxioms`. The latter remains transitively public
through the unchanged `AlgebraicSpace` import. All three stated construction
nodes remain used: `lem-trf-sheaf-pullback-diagonal`,
`lem-trf-fibre-product-atlas-tests`, and
`lem-trf-presheaf-pullback-etale-point-lifting`. No node or module is withdrawn.

The Hom-bijection clause of the diagonal lemma is unnecessary for the parent
assembly: Mathlib's chosen sheaf pullback already has the required categorical
universal property. This does not prune the diagonal node, which is still needed
for its representability clause. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The construction lemmas use
presheaf pullbacks, and two of them use the explicit compatible-pair cone,
whereas the item states results for chosen sheaf pullbacks. The private comparison
and transport helpers supply this missing glue. The node proof now records it.
The empty-family case is preserved because the joint-surjectivity proof transports
the dependency's extension-lifting condition without any nonemptiness assumption.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
