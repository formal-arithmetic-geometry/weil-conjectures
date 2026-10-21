## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_torsionSheaf_of_isProper`
in `Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange`, keeping its signature unchanged.
The chosen pullback isomorphism supplies `IsPullback`. The canonical comparison
`baseChange_eq_derivedBaseChangeMapPlus` identifies the exchange transformation with the
one in `isIso_baseChange_of_isProper`. For `F[0]`, degree-zero homology is isomorphic to
`F`; all other homology sheaves vanish by the single object's upper and lower bounds.
Their section groups are zero, so every section is killed by 1. This supplies the
required torsion-homology hypothesis and applies the stated bounded-below theorem.

The proof follows the existing three-step DAG plan and the current blueprint's
specialization to degree zero. It uses the same single-homology API as the private
calculation in `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`, without importing
that larger module. No new declaration, statement change, or definition change.

Validation: the item compiled through `lcompile.py` in 6.3 seconds, exit code 0,
with no diagnostics.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_torsionSheaf_of_isProper`
(node `prop-weil-proet-finite-proper-base-change`). No holes remain in the item, and no
holes are added or split off. The proof uses the project's stated bounded-below proper
base change theorem; this delivery does not claim to close its remaining dependencies.

## No longer needed

Removed the unused proof import `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
The proof uses the existing bounded-below single-functor and homology API instead of
that module's definition of torsion cohomology for module-valued unbounded complexes.
No declared mathematical proof dependency is pruned: all four nodes of the existing
plan remain relevant. No module is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No defect prevents the planned proof. The current blueprint additionally discusses
naturality and identity/pasting coherence; these are not clauses of the assigned Lean
signature, which remains unchanged. The proof uses equality of the actual canonical
transformations, so it proves invertibility of the requested morphism.

Searches: LeanFinder returned single-complex component lemmas; Loogle found
`DerivedCategory.singleFunctorCompHomologyFunctorIso`; the server grep search found
that isomorphism and `DerivedCategory.Plus.isZero_homology_of_isGE`. Local library
search found the existing proper base change theorem, its canonical comparison, and
the private single-object calculation noted above. No separate geometric argument or
new intermediate theorem is needed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
