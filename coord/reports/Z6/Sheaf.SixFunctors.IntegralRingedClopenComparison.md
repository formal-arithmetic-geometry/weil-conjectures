## What changed

Filled `WeilConjectures.IntegralSystemRealization.integralRingedClopenMap_isIso`
in `Sheaf.SixFunctors.IntegralRingedClopenComparison`, preserving its statement and
all public definitions. Added one proved private helper `ordinaryClopenReverse`.
The helper constructs the scalar-identified restriction presentation from the actual
site and ring adjunctions, then applies the existing reverse clopen adjunction.
Exact localization and uniqueness of right adjoints give an isomorphism from actual
open extension to actual derived direct image. The specified inverse-unit transpose
is then a composite of two isomorphisms. No normalization assumption is added.

Added private proof imports of
`Sheaf.AlgebraicGeometry.ClopenScalarRestrictionReverseAdjunction` and
`Sheaf.CategoryTheory.ExactDerivedAdjunction`. Updated the item's DAG proof to match.
Server single-file compilation succeeded in 8.8 seconds; its sole formatting
warning was corrected before delivery. Both new proof imports passed the import-cycle
checks. The delivery tool runs the final compiler and axiom checks.

The scalar reverse adjunction is a tool from the compact-support base-change unit:
it supplies the arbitrary-ring, ordinary clopen gluing consequence needed here;
its ordinary mode uses `lem-sf-clopen-reverse-module-adjunction`.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.IntegralSystemRealization.integralRingedClopenMap_isIso`
(node `lem-sf-integral-ringed-clopen-comparison`).
Added 0 holes. No `sorry` remains in the delivered module and no new module is added.
The proof uses already stated dependencies, including the existing
`SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction`;
this delivery does not claim to close that dependency's hole.

## No longer needed

No imports were removed and no module is withdrawn. The direct dependency on
`lem-pur-clopen-ringed-module-gluing` is replaced by the existing scalar reverse
adjunction interface. Gluing remains mathematically needed inside that interface;
this is not a claim to prune its module globally. The derived slice presentation
and integral coefficient data remain needed for the existing open-unit proof.
No tensor, strict-system, finite-level evaluation, or new intermediate theorem is
needed for this clopen comparison. The blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan described a fresh sectionwise comparison and its derived
normalization. Existing reverse-adjunction and exact-localization APIs suffice:
right-adjoint uniqueness gives the comparison, and full faithfulness makes the
specified transpose invertible without computing a normalized comparison.
The identity immersion, empty clopen, and zero coefficient ring all satisfy the
same argument; no cancellation of a nonzero section or nonempty scheme is used.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
