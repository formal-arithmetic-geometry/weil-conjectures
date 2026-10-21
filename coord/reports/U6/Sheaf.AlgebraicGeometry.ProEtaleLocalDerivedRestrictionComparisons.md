## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons`.
`inverseImage_exact` transfers additivity and finite-limit/finite-colimit preservation
through `proEtale_moduleInverseImage_comparison` and reflects them through the conservative
module forgetful functor. Abelian inverse-image exactness uses the existing generic flat
Kan-extension instances and adjunction; the module forgetful colimit instances are supplied
explicitly by `moduleSheaves_colimits_forgetful`.

`comparisons` uses Mathlib `Functor.copyObj` and `isoCopyObj` with exactly the prescribed
representative comparison. Its cohomology isomorphism composes the two canonical derived
homology isomorphisms with homology of alpha. Its shifted-single isomorphism composes alpha
inverse, the two canonical shift comparisons, and the shift of the two single comparisons.
Component formulas follow by definitional equality and reassociation.

All existing signatures, definitions and public imports stay unchanged. Added proof-only
imports of the generic flat Kan-extension module and `Mathlib.CategoryTheory.Adjunction.Additive`.
Updated the item's DAG proof, proof dependencies and proof origin to match this implementation.
The current module compiled cleanly through `lcompile.py` (39.2 seconds); no new modules or
intermediate statements were needed. The item does not realize a unit statement or proof step;
the recorded proper-base-change unit route is preserved.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.Scheme.ProEtaleLocalRestriction.inverseImage_exact`.
- `AlgebraicGeometry.Scheme.ProEtaleLocalRestriction.comparisons`.

Both belong to `lem-weil-pbc-local-derived-restriction-comparisons`.
Zero holes remain in the item; zero holes were added and zero statements were split off.
No existing statement was changed.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.SiteInverseImageTensor` and
`Sheaf.CategoryTheory.FiniteTypeRestrictionExact`.

The declared dependency `lem-weil-pbc-left-exact-site-inverse-image-tensor` is not applied:
the smaller generic flat Kan-extension instances directly establish the abelian finite-limit
preservation needed here, and the adjunction supplies colimits and additivity. Its module
remains a transitive import of `ProEtaleInverseImage`; this delivery does not withdraw it or
claim that it leaves the targets' closure.

The declared dependency `lem-weil-pbc-finite-type-restriction-exact` has a small-category,
same-universe interface. The already-imported `ringedOverFunctor_exactGeneral` from
`def-weil-pbc-ringed-derived-restriction` supplies the exact interface used here. The old
dependency is replaced in the DAG proof; no module is withdrawn.

The declared dependency `lem-sp-exact-functor-preserves-homology` is unnecessary: conservativity
and finite-(co)limit preservation reflect finite (co)limits directly, without first passing
through short-complex homology. The other original declared dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned short-exact-sequence reflection argument can be
shortened to direct reflection of finite limits and finite colimits. The original plan's
small-site restriction interface does not fit these independent universes directly; the
existing universe-independent interface already used by the item's instances fits exactly.
The current source, return records and rework list contain no return or quarantine entry for
this item. No definition repair, forced consumer adaptation, target change or new node is needed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
