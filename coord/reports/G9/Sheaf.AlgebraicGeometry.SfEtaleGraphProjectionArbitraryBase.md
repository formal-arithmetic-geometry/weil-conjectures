## What changed

Replaced the sorry of `AlgebraicGeometry.Etale.sfEtaleGraphProjectionArbitraryBase`
with a proof from the existing source invertibility theorem and the geometric
unit identity `AlgebraicGeometry.Etale.sfEtaleGraphUnitTensor`.
The latter is a new, strictly intermediate theorem in its own module: it is
step 6 of the accepted proof before the adjunction transpose, and states neither
the comparison's invertibility nor the final tensor square.

The item proves the transport of the comparison's adjunct into the exact
inverse-image model, proves inverse tensor-comparison naturality by a composite
natural isomorphism, then proves the tensor square by injectivity of the exact
sum/evaluation Hom equivalence and cancellation of the forward projection.
All existing public declarations, signatures and definitions are unchanged.
Unused public proof-plan imports were removed with a change record. No source-library module is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.sfEtaleGraphProjectionArbitraryBase`
(node `lem-sf-etale-graph-projection-arbitrary-base`).

Added one hole:
`AlgebraicGeometry.Etale.sfEtaleGraphUnitTensor`
(node `lem-sf-etale-graph-unit-tensor`). Its docstring gives the complete
clopen-transfer, projection-unit and exchange argument (old steps 2--6).
The item's two private helpers have complete proofs and introduce no holes.
This is a decomposition: one hole closed and one added, net zero holes.
The invertibility clause is proved using the existing source theorem
`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`.

## No longer needed

Removed the following private proof imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
- `WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `Sheaf.AlgebraicGeometry.EtaleOpenProjectionExchange`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.Topology.NoetherianSpace`
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
- `Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation`
- `Sheaf.AlgebraicGeometry.EtaleDerivedJointlySurjectiveConservative`

The parent no longer directly cites the following proof dependencies (those
used for the graph-unit identity remain dependencies of that new node):

- `lem-weil-pbc-proper-base-change`
- `def-weil-proper-morphism`
- `lem-weil-pbc-section-separated-closed-immersion`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-composition-cancellation`
- `def-weil-etale-morphism`
- `lem-pe-flat-lfp-monomorphism-open`
- `lem-weil-pbc-etale-sheaf-clopen-product`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-kun-derived-pullback-composition-monoidal`
- `def-pur-etale-exact-pullback-unit-composition-comparisons`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-pur-etale-open-derived-tensor`
- `lem-asd-open-projection-exchange`
- `lem-asd-open-base-change-unit-mate`
- `def-kun-projection-formula-map`
- `def-kun-unbounded-exchange`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-pur-unit-adjunct-tensor-action`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `def-weil-pbc-etale-shriek-base-change-map`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-finite-type-over-noetherian`
- `pqf-def-locnoeth`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-kun-finite-union-noetherian`
- `lem-sfb-noetherian-space-compact-subsets`
- `lem-weil-pbc-etale-fibre-discrete-separable-points`
- `lem-asd-clopen-geometric-sections-derived-evaluation`
- `def-weil-pbc-etale-sum-extension`
- `lem-etale-derived-jointly-surjective-conservative`

The explicit arbitrary-base graph geometry, fibre splitting and derived
conservativity calculation of old steps 8--11 is supplied by the source
invertibility theorem. Their modules are not claimed globally unused: the
source theorem and other library declarations may still need them.
The graph-unit node retains the dependencies of old steps 1--6, while the
parent node now records the actual three-part Lean argument. Its obsolete
top-level tool-use approvals are removed; no new approvals are invented.
Removed unused public proof-plan imports:

- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence`
- `Sheaf.CategoryTheory.UnitAdjunctTensorAction`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`

No Lean module currently imports the item; downstream search found no consumer
requiring adaptation. See `coord/changes/G9-sf-etale-graph-proof-imports.md`.

## Where the brief, the DAG or earlier work was wrong

The invertibility half was already proved in
`WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso`.
Reproving its arbitrary-base geometry and fibre argument is unnecessary.
No mathematical statement is disputed or weakened. The tensor compatibility
is additional content: the source invertibility theorem does not prove it.

## New nodes

`lem-sf-etale-graph-unit-tensor` states the geometric unit identity from
steps 2--6 of the accepted argument in the exact inverse-image model.
Its new module is `Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor`.
Empty schemes, zero coefficients, non-quasi-compact opens and arbitrary
unbounded complexes were checked in the natural-language proof; no extra
hypotheses are imposed.

`lem-sf-etale-graph-comparison-isomorphism` records the already existing
source theorem `AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`.
It creates no duplicate Lean declaration and no hole. Its statement is only
the invertibility clause, without the tensor square.

Change record: `coord/changes/G9-sf-etale-graph-proof-imports.md`.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
