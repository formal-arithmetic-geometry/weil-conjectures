## What changed

Completed the sole proof hole in `Sheaf.Paper.PointSystemTransportDescent`:
`WeilConjectures.PointSystemTransport.finite_evaluation`. The proof evaluates the
localization representative, proves the finite chain square from the normalized
restriction specification, applies the exact derived-square descent lemma, and
postcomposes with the finite comparison. The unchanged strict-system and finite
construction declarations are split into the new `PointSystemTransportChain` and
`PointSystemTransportFinite` modules and publicly re-exported. Three small proved
interfaces support the calculation: `ExactDerivedSquareDescent`,
`PointRestrictionSequenceEvaluation`, and `PointRestrictionSectionTransformation`.

## Proved and sorry left

Closed 1 of 1 sorries: `WeilConjectures.PointSystemTransport.finite_evaluation`
(node `lem-trf-point-system-transport-descent`). Added zero sorries. Every delivered
module compiles without `sorry`.

## No longer needed

The item no longer directly imports the private construction dependencies
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Sheaf.Paper.PointSystemEvaluationComparisons`,
`Sheaf.Paper.PointRestrictionSystemChainMap` (its `import all`),
the `import all` of `Sheaf.Paper.PointAutomorphismRestrictionNatural` (its public
import stays),
`Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism`, and
`Sheaf.Paper.PointSystemTensorTransition`; they remain used by the extracted
construction modules. No DAG dependency or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was corrected. The earlier monolithic file exceeded the
per-file compile budget after the proof was added; extracting the unchanged
construction into separately compiled modules makes the complete route compile.

## New nodes

`lem-trf-point-system-transport-chain`: `Sheaf/Paper/PointSystemTransportChain.lean`.
`lem-trf-point-system-transport-finite`: `Sheaf/Paper/PointSystemTransportFinite.lean`.
`lem-trf-exact-derived-square-descent`:
`Sheaf/CategoryTheory/ExactDerivedSquareDescent.lean`.
`lem-trf-point-restriction-sequence-evaluation`:
`Sheaf/Paper/PointRestrictionSequenceEvaluation.lean`.
`lem-trf-point-restriction-section-transformation`:
`Sheaf/Paper/PointRestrictionSectionTransformation.lean`.


## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 2 OK, 2 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.CategoryTheory.ExactDerivedSquareDescent": "84066f20785d06933df59c6905a4e6ec31e629e8", "Sheaf.Paper.PointRestrictionSectionTransformation": "bed5cf59d608d10be25a8739c709bbd7cdc3c110", "Sheaf.Paper.PointRestrictionSequenceEvaluation": "1e0028a540c326e606550a9a873a459e6b812f1a", "Sheaf.Paper.PointSystemTransportChain": "77a4b9464e34f58e10721b4fabecd34bc68fa773", "Sheaf.Paper.PointSystemTransportDescent": "e3b472088652e9d412112f6c5c85092f8c812b36", "Sheaf.Paper.PointSystemTransportFinite": "92f5e9d42c48880916ef448056fab8c286be0b68"}, "results": {"Sheaf.Paper.PointRestrictionWholeRoosSquare": {"hash": "eb5799b2c6579fdc42f87333fb32d36d5901a9fe", "status": "SLOW"}, "Sheaf.Paper.PointSystemNormalizedComparisonData": {"hash": "fa2a72ec24d2f533c7d6bc737477c3a7a1f63c0a", "status": "SLOW"}, "Sheaf.Paper.PointSystemPowerRoosData": {"hash": "91259c14ac7acb42ade3398312360eba52da7357", "status": "OK"}, "Sheaf.Paper.PointSystemRoosTransportData": {"hash": "6d0f8399764aa514a9c53586faf82f7343d009f3", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T07:15:56+0800", "transitive": 0, "version": 1}
```

Reviewer note (cc review of 4ee680c990cc): the two SLOW importers are pre-existing.
Timed concurrently at load ~50, PointRestrictionWholeRoosSquare takes 64.9 s against
this delivery and 72.2 s against the published build; PointSystemNormalizedComparisonData
takes 52.7 s against the delivery and 51.2 s published. The delivery slows neither, so the
earlier D4 Core and Coordinates/Calculus splits are not needed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
