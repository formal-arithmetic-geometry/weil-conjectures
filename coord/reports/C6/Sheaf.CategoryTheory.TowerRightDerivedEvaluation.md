## What changed

Proved `CategoryTheory.TowerRightDerivedEvaluation.exists_normalized` with its existing
signature and every clause unchanged. The module now constructs the comparison directly
from the two cochain units on K-injective complexes and descends it using Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`. The private descent proof proves naturality
on every derived morphism and the normalization on every complex. The canonical
resolution equation follows by postcomposing with the invertible evaluated unit and using
naturality. Transition compatibility follows from `Localization.liftNatTrans_app`, unit
naturality and cancellation on K-injectives, then naturality along a resolution.

Private helpers package the unchanged cochain unit as a natural transformation, prove its
invertibility on K-injectives and its resolution identity, descend comparisons, and compute
the existing localized transitions. No public declaration, definition or signature changes.
The original public imports are retained. Three backward-elaboration options are added
for the proof context; they export no notation or instances. The command-checker record is
`coord/changes/C6-tower-right-derived-evaluation-proof-context.md` (open). Removed the two unused private proof imports
listed below. Updated the existing node's proof, proof dependencies and proof origin to
match the Lean argument. The unit record has no realized steps and its route is unchanged.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.TowerRightDerivedEvaluation.exists_normalized`
(node `lem-coef-tower-right-derived-evaluation`).

Added zero holes and split off zero statements. No `sorry` remains in the delivered module.
Every private helper is proved. Evaluation's K-injectivity theorem and the universal derived
pair are reused from the library; no stronger resolution, exactness, adjunction, boundedness
or product hypothesis is introduced.

## No longer needed

Removed private imports `Sheaf.CategoryTheory.KInjectiveExactSquareComparison` and
`Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.

The proof no longer uses nodes `lem-weil-pbc-kinjective-exact-square-comparison` and
`lem-sf-kinjective-derived-map-computation`: their formulas are replaced by direct descent
and direct cancellation of the explicitly defined canonical resolution comparison.
The lower Mathlib leaf `lem-weil-pbc-kinjective-hom-derived` is used instead.

The original redundant proof dependencies `def-weil-pbc-additive-functor` and
`def-weil-inverse-system` are still statement dependencies; additivity and tower transitions
are handled by Mathlib's existing instances and definitions. No library module is withdrawn;
the two removed proof modules may still have other consumers.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The homotopy-level exact-square theorem
is valid, but directly using it requires substantial transport of its normalization through
both Q/Qh and the homotopy composition comparisons. Constructing the same comparison from
the already transported cochain units avoids those transports. This also proves the unit
normalization on every complex before deriving the resolution formula, reversing the order
of those two parts of the original plan. Existing naturality suffices for the transition
calculation; the full derived-map computation theorem is unnecessary.

Validation: the single-file server compile passed cleanly in 14.9 seconds. The first
delivery attempt pushed nothing because its static command check required the above
change record for the elaborator options; this packet supplies that record. Public
signature and `cochainUnit` body comparisons are identical to the original source.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
