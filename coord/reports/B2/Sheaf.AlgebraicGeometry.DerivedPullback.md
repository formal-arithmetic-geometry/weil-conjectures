## What changed

Repair the zero-hole duplicate derived-pullback construction by using
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, whose functor transports
`Scheme.Modules.derivedPullback` along `schemeDerivedCategoryEquiv`. Its complete
`derivedPullback_spec` proves the exact inverse-image, tensor-counit universal property,
triangulated structure and K-flat counit invertibility required by the existing node.
No source-library file or target statement is changed.

Migrate the live reverse import closure together, including the newly live
`OpenFlatComplexStalkCounit` consumer identified by the returned landing.
Twenty-eight consumer copies, plus the assigned duplicate, are withdrawn in favor of their adopted source modules;
eleven consumers retain their actual additional declarations and proofs, with imports
redirected and `IsAcyclicTensorKFlat` renamed to `IsKFlatTensor`. The resolution
predicate is correspondingly `IsKFlatTensorResolution`; both source definitions have
the same mathematical content. The source functor is canonically isomorphic to the
former resolving-class choice, rather than asserted equal to that arbitrary choice.
The unused data wrapper `derivedPullbackData` and `derivedPullback_eq_choose` disappear.

`PerfectHomTransportExtension` supplies the three names absent from its main source
module. `PerfectHomComparisonTriangle` retains public `compositionTo`,
`compositionTo_triangle`, and `perfectHomComparison_symm_eq_compositionTo`: source
triangle helpers are private. Its duplicate main theorem is supplied by a public
source import; its helper proof uses the source extension's private associativity
lemma through `import all`. Remove a redundant local irreducibility attribute because
the source derivedPullback is already irreducible. Clean two pre-existing linter
warnings in the adapted abstract projection-tail proof.

The original ten retained Lean modules compiled remotely, each in less than 15 seconds.
This repair compiled all eleven retained modules against the current server build
without errors or warnings; `OpenFlatComplexStalkCounit` compiled in 9.2 seconds. Its only edits redirect the public and private imports
of `SingleComplexBaseChangeStalkCondition` to the adopted source module; the
`derivedPullback`, `tensorPullbackAdditive`, and `counit` uses retain their signatures
and proofs. The change record now includes this consumer in `## Users`.
The current main-20261015 blueprint definition and the Stacks cohomology
section-derived-pullback / lemma-derived-base-change were read against this route.
Searches: LeanFinder returned underived sheaf pullbacks; Loogle and Mathlib grep
identified Functor.leftDerivedNatIso and isLeftDerivedFunctor_iff_of_iso, exactly
the uniqueness and transport results used by the source specification.
A separate axiom probe of source `derivedPullback`, `exists_derivedPullback`, and
`derivedPullback_spec` reports only propext, Classical.choice, and Quot.sound.
The DAG attachments of all withdrawn modules point at the corresponding source
statements; mathematical dependencies and unit steps stay. The assigned node's final
proof step now records transport from module pullback and uniqueness of derived
functors rather than equality with a chosen existential witness.

Definition review of target meanings should verify the canonical isomorphism between
the old K-flat-resolving-class construction and the transported module construction.
No target declaration text is edited. The source specification proves exactly the
universal property and K-flat representation used by consumers.

Repair of return C-20359 (returned head `20359895ce`): reread the current
`AffineDerivedPullbackModuleModel` after import-pruning commit `31a67ea366`.
Its current theorem is still the duplicate covered by the reviewed withdrawal;
the adopted source theorem remains its replacement. Preserve that withdrawal,
all source declarations, and the node attachment to the source theorem. Compare
all eleven retained consumers with the current shared sources before compiling.
The delivery tool fetches `sheaf-dag` and constructs a new commit directly on that
base, so the old overlapping patch is not reused. Current source hashes are
recorded in the sandbox scratchpad for this comparison.

## Proved and sorry left

Assigned item: 0 original sorry, 0 sorry remaining. Holes closed: none. Holes added:
none. This is a definition/duplicate repair, not a new proof or decomposition.
All eleven retained consumers have zero sorry. All withdrawn modules also had zero
sorry; their adopted source proofs are retained. No new nodes or unfinished lemmas.

## No longer needed

Withdraw the following duplicate modules, redirecting their live importers and DAG
attachments to the proved source implementation:

- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel` → `WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackModuleModel`.
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` → `WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
- `Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison` → `WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison`.
- `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology` → `WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology`.
- `Sheaf.AlgebraicGeometry.DerivedPullback` → `WeilConjectures.AlgebraicGeometry.DerivedPullback`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCoherence` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionIsIso`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackKFlatTensorModel`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackRecordedComposition` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorAssociativity`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct` → `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct`.
- `Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus` → `WeilConjectures.AlgebraicGeometry.DerivedSingleOpenLocus`.
- `Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh` → `WeilConjectures.AlgebraicGeometry.DerivedTensorPreservesQCoh`.
- `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit` → `WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit`.
- `Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData` → `WeilConjectures.AlgebraicGeometry.OpenRestrictedRepresentativeData`.
- `Sheaf.AlgebraicGeometry.PerfectDerivedTensor` → `WeilConjectures.AlgebraicGeometry.PerfectDerivedTensor`.
- `Sheaf.AlgebraicGeometry.PerfectDescentOnOpen` → `WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen`.
- `Sheaf.AlgebraicGeometry.PerfectHomCochainCounit` → `WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit`.
- `Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare` → `WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare`.
- `Sheaf.AlgebraicGeometry.PerfectHomTransport` → `WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension`.
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison` → `WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison`.
- `Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison` → `WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison`.
- `Sheaf.AlgebraicGeometry.RelativeTensorPullbackKFlatModel` → `WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackKFlatModel`.
- `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` → `WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`.

The repair also removes the public and private imports of
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` from
`OpenFlatComplexStalkCounit`, replacing both with the source counterpart.

The assigned module no longer imports Sheaf KFlat, KFlatResolution,
InverseImageExactKFlat or TensorPullbackKFlatQuasiIso. Their mathematical results remain
needed in the adopted source construction, so those nodes are not claimed pruned.
No blueprint unit statement or unit step is removed. No source declaration is removed.
Quarantined consumer archives are preserved; restored work must migrate their imports
to the source module and use its IsKFlatTensor API, as the live consumers do here.

## Where the brief, the DAG or earlier work was wrong

The assigned module already contained a complete proof and zero sorry. The current
retirement manifest lists it as DIFFERENT, with the old fixed-choice API; the source
now has the same derivedPullback name as an irreducible transported construction.
Combining the two imports produces the duplicate-name failures recorded in rework.tsv.
The old equality-to-choice API is not an equation about this new construction and is
not retained as an unsupported theorem. No external live or quarantined consumer uses
that equation or the data wrapper.

The apparent names missing from PerfectHomTransport are in the existing source
PerfectHomTransportExtension. The apparent public composition helpers in the source
PerfectHomComparisonTriangle are private; the retained Sheaf helper module preserves
that public API without duplicating the source main theorem.

Change record: `coord/changes/B2-derived-pullback-source-construction.md`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
