## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.canonical_section_projection_core_precomposition`
in `Sheaf.Paper.CanonicalSectionProjectionCorePrecomposition`, with its statement unchanged.
The private categorical calculation composes the symmetry-ordered projection mates, transposes
along the composite adjunction, and cancels by oplax unit coherence. The existing derived
pullback identity and composition equations verify the canonical section comparison at the
unit. The normalization of `projectionMap` then transports the result through the existing
fixed tensor bundle. The categorical helpers in the item are proved and private. The new
auxiliary module `Sheaf.Paper.CanonicalPullbackSectionUnit` proves the canonical section
unit formula.

Added proof imports for `ProjectionMapCompat`, `CanonicalPullbackSectionUnit` and
`DerivedCategory.Monoidal.Braided`. The new helper publicly imports `UpperStarUnitCoherence` and
`CondensedModuleDerivedPushpull` for its statement. No exported interface of an existing
module changed. Updated the item's DAG proof to this direct route.

Both delivered modules compile without warnings: the auxiliary module in 18.2 seconds,
and the item in 20.1 seconds. The existing theorem signature is textually unchanged.

## Proved and sorry left

Closed the sole hole in
`AlgebraicGeometry.ProEtale.RationalP1.canonical_section_projection_core_precomposition`
(node `lem-sfb-projective-canonical-section-projection-core-precomposition`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.
No obligations are split off. Also proved
`AlgebraicGeometry.ProEtale.CondensedRing.canonicalDerivedPullbackSectionUnit`
(node `lem-sfb-canonical-derived-pullback-section-unit`) without adding a hole.

## No longer needed

No imports removed and no modules withdrawn. All three declared dependencies remain necessary
for the statement's canonical constructions. The prose plan's transport through a separate
ringed-module comparison is unnecessary: the existing native derived pullback oplax structure
and its unit coherence give a direct categorical proof. No new tensor-composition or section
coherence obligation is required. This does not bypass any step of the unit route.

## Where the brief, the DAG or earlier work was wrong

The prior plan hid the needed coherence behind a transport without specifying an applicable
ringed comparison. Here only coherence at the tensor unit is needed, rather than a general
binary tensor-section theorem. The existing source-library unit-coherence results supply it.
The item statement, its definitions, and the unit route are preserved.

## New nodes

`lem-sfb-canonical-derived-pullback-section-unit` records the fully proved formula for the
canonical section comparison at the tensor unit, for arbitrary section/retraction maps.
Its module isolates the source unit-coherence calculation from the projective-line instance
aliases. Typed private aliases share the canonical compositor and functors during
kernel checking. Its comparison parameter is identified with the canonical composite by an
explicit defining equality. The identity-section case reduces to the published identity unit
equation; no nonemptiness or geometric finiteness assumption is needed. It adds no `sorry`,
target hypothesis or choice of data. No change record is required.

## Related modules compiled before delivery

26 related module(s) compiled against this delivery by deliver3.py: 26 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalPullbackSectionUnit": "e8ac6924d4e087178c0f9fd7a8fa6e4f3f641225", "Sheaf.Paper.CanonicalSectionProjectionCorePrecomposition": "529834dcd5d8e915d44aa62ccc2b60cd2b749918"}, "results": {"Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded": {"hash": "d2fc5b1116689ece42eba428627c270ff7c0dfeb", "status": "OK"}, "Sheaf.Paper.CanonicalSectionProjectionCoreCoherence": {"hash": "6bf2aa7d1e5a309a8f7b6bec01e5e11e2ef471d7", "status": "OK"}, "Sheaf.Paper.CanonicalSectionProjectionTransport": {"hash": "3cd0b52aaa994fd7ba80fcf58287cbdccae268d7", "status": "OK"}, "Sheaf.Paper.DerivedPoincarePairing": {"hash": "ac0ec8286de32e48b3e3caebd6080cde12c91c24", "status": "OK"}, "Sheaf.Paper.FiniteProjectionOperationPresentation": {"hash": "ad72beff432c0861f6c5e15720fbc3af945c67f0", "status": "OK"}, "Sheaf.Paper.NormalizedOrientationPerfectDuality": {"hash": "145740e6c5f67bc36ee7e1685fb1db5db7f77808", "status": "OK"}, "Sheaf.Paper.ProjectionFormulaCoherence": {"hash": "13929edce12d5ca05c2586b744f63881a5c1f9f4", "status": "OK"}, "Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor": {"hash": "2491ac817143b1bdee9034d2173f87d3bae3aef2", "status": "OK"}, "Sheaf.Paper.SixFunctorMixedSupportCupProduct": {"hash": "f9f80cc388a0f3193b0014a954198765a9b98e8f", "status": "OK"}, "Sheaf.Paper.TensorHomExchange": {"hash": "220d046d5b668a7f1aaab68abea931d9b7b3f9b2", "status": "OK"}, "Sheaf.Paper.TensorMapPresentationIndependent": {"hash": "1a4a0d66ca299c022d98263c06146f5e6bc14428", "status": "OK"}, "Sheaf.Paper.TensorMateInvertibleInput": {"hash": "5a0d965732100b8248a112108951c6d593f0f56f", "status": "OK"}, "Sheaf.SixFunctors.FiniteAdjunctionDiagramData": {"hash": "44282e47115f827dc7119587dbb29b77580a2c03", "status": "OK"}, "Sheaf.SixFunctors.FiniteAdjunctionSystemData": {"hash": "5384396ad97a828cbff89189041d95c436c8e3ad", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicBidualComparison": {"hash": "1771fe5d0709a59c10696374c8a352f48fc54400", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicTensorRealization": {"hash": "f4db51c21f31afade083f7064add106c4b195f31", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry": {"hash": "725d0bc8686fb680a169e8e6a974ea9148b13bb7", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryExtension": {"hash": "f12e2cb63a1a7f3d4af22e5ef3027f14df4fd68e", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryResolving": {"hash": "ea70120a4f4644d72812819c4ac5778954d93928", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality": {"hash": "ca4e9d4a6bb7b41c2bb4b29b971ac5dda95e1da7", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualExceptionalSystem": {"hash": "fa016b24d8cfa6968447d59f46b0e8039a8e0c7a", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalDescendedCounit": {"hash": "c9843f6bed89c03ce178c16fdda83efb97e986ae", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction": {"hash": "4cb63c4e27d0be274a5c4afb21fbc9031b6afbbb", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalMappingSystem": {"hash": "c06bf153e52e4cfced26aa8c141827ea7671d493", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierSignedCalculus": {"hash": "ed1dbd048bd09c9547ed901e651607feaf98119e", "status": "OK"}, "Sheaf.SixFunctors.SystemTotalEnrichedTranspose": {"hash": "7d1dee308ca33c71387eb1f6f2be5eedcc8147bf", "status": "OK"}}, "seconds": 171, "time": "2026-10-28T13:56:24+0800", "transitive": 25, "version": 1}
```

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
