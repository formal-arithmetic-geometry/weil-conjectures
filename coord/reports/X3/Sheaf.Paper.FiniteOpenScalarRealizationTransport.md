## What changed

Proved `AlgebraicGeometry.Scheme.FiniteCompactScalar.fixedOpenScalar_realization_transport`
in `Sheaf.Paper.FiniteOpenScalarRealizationTransport`, preserving its complete signature.
The proof first establishes the realization/restriction cube before localization, then
localizes it, verifies the unit normalization of `realizationScalarIso`, and transports
inverse scalar mates using `equivalenceAdjunctionComparison_inverseMate`.
The complete file compiled through `lcompile.py` in 28.5 seconds with no `sorry`.
All added helpers are private and proved. The four additional imports are proof imports;
the existing public import and all public interfaces are unchanged.

The proof reuses the existing private helper `square_symm_hom` from
`DerivedExactSquareComposition`, and `forward_realization_mate` from
`ProEtaleOpenScalarRestrictionCoherence`, via `import all`.
The other proof imports supply exact localization of commutative cubes and normalized
inverse-mate transport. The item's DAG proof and dependencies now record this assembly.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.fixedOpenScalar_realization_transport`
(node `lem-finite-open-scalar-realization-transport`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0. No statements were
split off, and no definitions or existing statements were changed.

## No longer needed

None. The original import and all originally declared dependencies remain needed.
No module or node is withdrawn. The unit's route remains the realization face of the
open scalar comparison; no site comparison is substituted for it.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid. The existing library contains enough proved generic
coherence lemmas to implement it without another split. One normalization detail
requires proof: `Equivalence.mapDerivedCategory` is constructed by `Equivalence.mk`,
which adjusts the unit. Equality with the exact localized adjunction follows from
counit equality and adjunction uniqueness, rather than definitional equality of units.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
