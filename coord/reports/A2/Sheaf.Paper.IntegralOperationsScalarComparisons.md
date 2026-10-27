## What changed

Proved the internal-Hom completeness theorem in
`lean/Sheaf/Paper/IntegralOperationsScalarComparisons.lean`. The proof first establishes
local principal completeness on a small ringed site by the tensor-Hom adjunction, then
transports it through the native small-site equivalence. The strict Roos completeness
criterion identifies this predicate with the recorded `IsSfDerivedComplete`.

Rebased the returned packet against current sheaf-dag. F9 has independently landed
all three supporting proofs in `lean/Sheaf/Paper/IntegralScalarExtension.lean`.
Reviewer note (2026-10-25, 88ed40c139f): the delivered transparency change there
(`abbrev`→`def integralOrdinaryDerivedScalar` and two new global instances) was not
forced and is withdrawn; `IntegralScalarExtension.lean` stays at its published (F9)
version, against which the item compiles unchanged.

Long representative formulas are stored in nine named normalization predicates, without
changing their formulas. Chosen comparison maps have explicit copies of their existing
types (including `scalarIntegralClosed` and `scalarIntegralModels`). These
definition/interface changes are recorded in
`coord/changes/A2-scalar-normalization-predicates.md`,
and `coord/changes/A2-scalar-map-explicit-types.md`;
`coord/changes/A2-ordinary-derived-scalar-transparency.md` is marked withdrawn.

The repaired packet compiled on the server with `lcompile.py --all`. An initial
comparison-module timeout was followed by a successful profiling run of both modules;
the temporary profiling option is removed. `deliver3.py` recompiles the final files
and runs the preflight dry run before pushing.
Consumer checks passed for the direct scalar-functor users listed in the change records,
including both exactness consumers and the two algebraically closed coefficient consumers.
The original SfScalarExtensionComposition and FrobeniusSquareExchange checks timed out;
no consumer interface error remains in the checked files.
No source-library module was modified.

## Proved and sorry left

Original item holes closed: 1 of 13. No holes added and no statements split off.

- `WeilConjectures.scalarInternalHom_complete`.

Supporting module: zero holes left. Its three proofs were present in the returned
packet, but all three are now already proved on current main by F9, so this repair
claims no new supporting closures. Their names, under node
`def-weil-integral-scalar-extension`, are:

- `WeilConjectures.integralCompletedScalarMap_existsUnique`.
- `WeilConjectures.integralOrdinaryScalarWitness`.
- `WeilConjectures.integralOrdinaryScalar_exact`.

Remaining item holes (all unchanged conclusions under
`lem-pur-integral-operations-scalar-extension`):

- `WeilConjectures.scalarPullbackLevel_existsUnique`.
- `WeilConjectures.scalarPullbackTower_existsUnique`.
- `WeilConjectures.scalarTensorLevel_existsUnique`.
- `WeilConjectures.scalarTensorTower_existsUnique`.
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`.
- `WeilConjectures.scalarTensorOrdinary_existsUnique`.
- `WeilConjectures.scalarCompletion_existsUnique`.
- `WeilConjectures.scalarOrdinaryTensorChain_existsUnique`.
- `WeilConjectures.scalarClosedTensor_existsUnique`.
- `WeilConjectures.scalarHomOrdinary_isIso`.
- `WeilConjectures.scalarOperationsOrdinary_tower`.
- `WeilConjectures.scalarOperationsOrdinary_unit`.

The pre-existing proved declarations `scalarRoosMap_existsUnique`, `scalarGood`, and
`scalarHomOrdinary_naturality` remain completely proved. The Roos proof is refactored
through two proved private cocone maps; no hole is hidden in a definition or helper.

## No longer needed

Removed these proof imports; the completed portion uses the local vanishing argument
and native restriction, and the retained public imports already provide declaration types:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`.
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `Sheaf.Paper.DerivedCompleteKoszulReconstruction`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`.

No module is withdrawn. No original DAG dependency is claimed globally unnecessary:
the original plan still describes the remaining holes. No UNIT statement or realized
proof step is bypassed. The node records add the dependencies of the completed local vanishing proof
only; the supporting node retains the already landed route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was weakened or disputed. Long inferred types repeatedly
unfolded the coefficient completion and derived-category constructions, so explicit
types and named normalization predicates were needed to keep their interfaces usable.
The DAG's source attachment for integral scalar extension is the independent-universe
wrapper; its same-universe implementation now has zero holes on current main.
The wrapper attachment and its declarations are preserved.

No new nodes and no forced adaptations. Consumer timeouts are distinguished from type
errors; for example `FrobeniusSquareExchange` times out also against the original published
scalar functor.

The additional completion/tensor/Hom proof experiments exceeded the compile limit.
They are not counted as closures or included as new obligations in this packet.


Repair of return C-ab786, head `ab78695abb4`: the review passed, but its landing
failed before merging because the reviewer fix used a change-record basename as
its alias. `tools/batch_land.py` maps `coord/changes/<stem>.md` to
`<stem>.change.md`. The three repository records are included under their full paths;
any reviewer fix must use these exact aliases:

- `A2-ordinary-derived-scalar-transparency.change.md`.
- `A2-scalar-map-explicit-types.change.md`.
- `A2-scalar-normalization-predicates.change.md`.

This repair includes the alias clarification in the affected change record and
reconciles the supporting Lean file and node with F9's current landed proofs.
No modification to the landing tools is proposed or made.

## Forced adaptations

None. (The unforced change to `Sheaf.Paper.IntegralScalarExtension` was withdrawn by the
reviewer.)

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
