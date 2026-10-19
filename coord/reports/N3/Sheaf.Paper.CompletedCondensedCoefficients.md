## What changed

`completedCondensedPullback` is now proved. The proof uses two private generic helpers:
one transports ring-object comparison naturality across a monoidal functor comparison, and the
other transports a normalized inverse-limit cone across that comparison. The five conjunction
clauses are then discharged by the naturality theorem, the existing integral comparison, the
existing algebraic-closure cocone theorem, and preservation of the finite-subfield colimit by
the inverse-image functor. The theorem statement is unchanged.

`completedCoefficient` was changed from `noncomputable abbrev` to an identical regular
`noncomputable def` to prevent repeated expansion during elaboration. The direct downstream
consumer `Sheaf.SixFunctors.IntegralModelsGenerators` was compiled unchanged. The change is
recorded in `coord/changes/completedCoefficient.md`.

## Proved and sorry left

Closed one of the five original sorries: `AlgebraicGeometry.ProEtale.completedCondensedPullback`.
Four original sorries remain in this module: `completedCondensedIntegral`,
`completedCondensedRational`, `completedCondensedPadicIntegral`, and
`completedCondensedPadicRational`. All four are attached to node
`sk-prop-sfb-qlbar-colimit-x`. No new sorry or new node was added.

The item compiled cleanly in 34.7 seconds; the unchanged consumer compiled in 28.5 seconds.

## No longer needed

No imports were removed. The node no longer needs `lem-galois-yoneda-hom-bijection`,
`lem-galois-yoneda-fully-faithful`, or `det-pe-topos-functoriality-site` as direct
proof dependencies: naturality and normalized cone transport replace that calculation.
The pullback proof does not directly use the blueprint's separate
rationalization, finite-subextension, Yoneda, or tensor-universal-property dependencies;
those remain relevant to the other declarations and are not imported by this module. The
attempted cyclic imports of `Sheaf.Paper.PadicIntegersInvertEll` and
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` were discarded because each
already reaches this module.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes the mathematical construction at a higher level than the
available declarations. The usable Lean route is the existing normalized integral comparison
and algebraic-closure cocone theorem, combined with generic monoidal naturality and cone
transport. The earlier telescope route was cyclic and could not be imported. No target
statement was changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
