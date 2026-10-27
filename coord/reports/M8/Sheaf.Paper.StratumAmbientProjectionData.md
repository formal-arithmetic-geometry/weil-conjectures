## What changed

Proved `AlgebraicGeometry.ProEtale.stratumAmbientHomComparison` in
`Sheaf.Paper.StratumAmbientProjectionData`, preserving its signature and public imports.
All additional imports serve the proof. Private proved helpers transport open/closed
localization to the specified constant coefficients, establish both unbounded projection
formulas, compose them, and apply the tensor-Hom adjunction and parametrized conjugation.
Updated the existing node's proof and dependencies to describe this argument.
The required file-level command record is
`coord/changes/stratumAmbientHomComparison-proof-commands.md`; it records all 21
downstream modules and the preserved public theorem signature.

The closed projection is checked by the closed counit and complementary-open vanishing.
The open projection is the adjunction transpose of tensor pullback; its two restrictions
are invertible by the open unit and disjoint-support vanishing. The resulting isomorphisms
are natural in both variables. The final comparison is obtained by adjunction conjugation.
No boundedness, constructibility or Tor-amplitude assumption is introduced. Empty strata
and zero coefficient rings are allowed by the same categorical zero-object arguments.

Validation: the complete file compiles through `lcompile.py` without errors or warnings.
The delivery tool performs the independent compile and axiom probes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.stratumAmbientHomComparison`
(node `lem-weil-stratum-ambient-hom-comparison`).

Zero holes remain in the item. Zero holes added and zero statements split off.
All new private helper declarations are proved. Existing imported statements are used
as the stage-3 dependency interface; this does not assert that their transitive axiom
closure is already sorry-free.

## No longer needed

No original imports removed. No node or module withdrawn: the assigned node originally
had empty proof dependencies, so there is no obsolete declared dependency to remove.
The proof uses support detection to establish the open projection directly; it does not
need a new ringed-slice K-flat descent lemma or a comparison between the fixed-scalar
and intrinsic derived tensor structures. In particular it does not import
`Sheaf.AlgebraicGeometry.ProEtaleOpenTensor`,
`Sheaf.Paper.OpenImmersionTensorPiece`, or
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`.

## Where the brief, the DAG or earlier work was wrong

The item's previous node described the entire comparison with no declared proof
dependencies. The existing ringed localization, native tensor-Hom and tensor-pullback
interfaces suffice, together with the support arguments written in this delivery.
The generic private conjugation helpers in `EtaleGenericStratumMate` are independent
of etale geometry and apply unchanged to the pro-etale categories.
No statement or definition correction was necessary.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
