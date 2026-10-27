## What changed

Filled `AlgebraicGeometry.Etale.properOpenDerivedUnitNormalization` using the ordinary
support normalization and the canonical localization factorization equations. Added
private, proved helpers for the ordinary adjunction calculation, homotopy transport,
and localization of the triangle. The coefficient-category argument is proved
before specialization to module sheaves, keeping kernel checking within the time limit.
Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality`.
The public signature and public imports are preserved.

Updated `lem-cbc-proper-open-derived-unit-normalization` to describe the direct
localization calculation. The unit route is preserved. No definitions changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.properOpenDerivedUnitNormalization`
(`lem-cbc-proper-open-derived-unit-normalization`). One original hole, zero remaining
holes, zero added holes, zero split-off statements. This is a proof, not a decomposition.

## No longer needed

`lem-weil-pbc-mate-pasting` is not needed by this proof: direct naturality and the
published unit/counit localization formulas suffice. No original public imports were
removed, and no module is withdrawn. In particular this does not claim that the general
mate-pasting module is unnecessary for other users. The proof does not use
`Adjunction.derivedPlus_mateEquiv_app_fac`; it uses the simpler counit factorization.

## Where the brief, the DAG or earlier work was wrong

The planned passage via the derived mate factorization is unnecessary. The ordinary
unit equation localizes directly by retaining the p-pushforward derived unit, moving it
through the compositor by naturality, and applying `derivedPlus_counit_app_fac`.
Only exact comparison isomorphisms are canceled. This works for the empty open and the
zero coefficient ring without additional hypotheses.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
