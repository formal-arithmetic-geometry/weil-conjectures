## What changed

Proved `AlgebraicGeometry.Etale.derivedGeometricStalkIso` with its entire signature unchanged.
The proof uses the existing generic `Etale.upperStarCompSheafFiberIso` in `ModuleCat A`,
lifts it with the derived composition and natural-isomorphism comparisons, applies the
stalk functor to the given isomorphism, and uses `mapDerivedCategoryFactors`.
The natural `Point.constantSheafCompSheafFiberIso` then supplies a chain isomorphism
through `mapHomologicalComplexCompIso` and `mapHomologicalComplexIdIso`; localization
finishes the proof. There is no boundedness assumption or choice of representatives.

Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.
Updated the item's DAG proof, proof dependencies and proof origin to this direct route.
No definitions, theorem signatures, universes or target statements were changed.

## Proved and sorry left

Closed the original single hole in `AlgebraicGeometry.Etale.derivedGeometricStalkIso`
(node `lem-sf-etale-stratified-stalk-identification`).
Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No intermediate statements or new holes were introduced.
The proof compiled through the required remote single-file compiler, including after
removal of the unused imports. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

## No longer needed

Removed these imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The first, second and fourth modules' declarations are unnecessary because the proved
generic stalk comparison already works directly in `ModuleCat A` for arbitrary scheme
morphisms. The specialized abelian-group constant-stalk comparison is replaced by the proved
generic natural comparison in `ModuleCat A`. Its existing public import
`WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk` is retained to preserve
the module's public interface for existing consumers. The pointed-stalk
wrapper is unnecessary because `geometricStalk` uses `Point.sheafFiber` directly.
The abstract geometric-stalk definition and constant-stalk mathematical result remain
in the DAG proof; their particular specialized modules are not used by this proof.

Removed proof dependencies and their now-unused tool approvals:
`lem-weil-pbc-geometric-point-pullback-stalk`,
`lem-weil-pbc-inverse-image-composition-module-linear`, and
`prop-weil-pbc-inverse-image-modules-exact`.
The last remains a statement dependency of the unchanged original node.
The replacement `lemma-openclosed-stalk-upperstar` is already Lean-closed and its exact
source-library declaration is used. No unit statement or unit proof step is bypassed;
`sk-prop-sf-biduality-general` has no realized step attached to this auxiliary node.
These removals describe this proof's dependencies; no claim is made that the removed
modules are globally unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically sound but unnecessarily passed through global
sections on the algebraically closed point and a different module-sheaf encoding.
The library already provides both required natural comparisons directly in the
coefficient category used by the statement. The scalar and differential compatibility
therefore come from their typed natural isomorphisms without new comparison lemmas.
Edge cases remain covered: the zero ring and zero complex require no exceptions;
for an empty source scheme the geometric-point parameter has no inhabitant; the
identity morphism is an immediate specialization of the same comparison.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
