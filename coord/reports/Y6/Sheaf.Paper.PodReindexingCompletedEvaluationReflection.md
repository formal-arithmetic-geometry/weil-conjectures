## What changed

Reduced `WeilConjectures.PodCompletedReflection.signed_shifts` to the separate
completed tensor signed-shift normalization result
`WeilConjectures.podNormalized_tensor_signed_shifts`. The assembly supplies the
ordinary chain/derived Hom shifts from `comparison_exists` for the given comparison
and obtains both Roos coordinate equations directly from the given completion laws.
The item retains its original theorem signatures, definitions and public imports.

Exposed the existing complete reconstruction proof as
`WeilConjectures.purNormalizedReconstructionOfScheme` in
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`. Its original proof does
not use its geometric invertibility binder. The original theorem keeps its exact
signature and docstring and specializes this proved helper. The item reuses it
instead of duplicating the private reconstruction argument. No definition changes
and no consumer adaptations are required.

All three delivered Lean modules compile together with lcompile.py --all (exit 0).
The delivery tool will perform the required independent preflight checks.

## Proved and sorry left

Original holes: 3. The proof closes `WeilConjectures.PodCompletedReflection.signed_shifts`
by decomposition into one strict part of its three-part conclusion, verified by successful
full-module compilation. Its ordinary Hom-shift and Roos parts have actual Lean proofs.
This is a decomposition, not a net reduction of holes.

The two original holes retained are
`WeilConjectures.PodCompletedReflection.reindexing_laws` and
`WeilConjectures.PodCompletedReflection.identity_composition`, both attached to
`lem-pod-reindexing-completed-evaluation-reflection`.

One hole is added: `WeilConjectures.podNormalized_tensor_signed_shifts`, attached to
`lem-pod-normalized-tensor-signed-shifts`.

Actual textual hole count across delivered Lean files: 3 (2 retained, 1 added).
`WeilConjectures.purNormalizedReconstructionOfScheme` and every other declaration
in the adapted reconstruction module are proved, with zero holes in that module.
No private declaration or definition contains a hole.

## No longer needed

The item removes direct proof imports of `Sheaf.Paper.NormalizedDVREffectivity`,
`Sheaf.Paper.CoefficientSequenceRoosModel`, `Sheaf.Paper.CoefficientConstantTowerRoos`,
`Sheaf.Paper.NormalizedDVRKFlatReductionModel`,
`Sheaf.Paper.NormalizedDVRKFlatTransition`, and
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
Their reconstruction work is reused through the proved shared helper. The corresponding
DVR/Roos nodes remain indirect dependencies through
`lem-pod-unrestricted-normalized-reconstruction`, rather than direct dependencies of
the item. No module is withdrawn or globally pruned. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The completion/tensor dependency supplies signed tensor shifts for its particular
existentially supplied normalized family. The item quantifies over arbitrary normalized
completion and tensor data. The new lemma isolates precisely that representative
normalization step; the ordinary Hom-shift and Roos clauses already follow from the
stated declarations. The new statement is strictly only one part of signed_shifts.

The geometric invertibility assumption on `purNormalizedReconstruction` was unused in
its complete proof. Exposing that proof at its actual generality avoids duplication and
preserves every existing consumer's signature and meaning.

An attempted completed-evaluation assembly has been retained only in the scratchpad;
it is not part of this delivery. Its two draft auxiliary modules were never delivered
and are not included. The original reindexing_laws remains explicit and unchanged.

## New nodes

`lem-pod-normalized-tensor-signed-shifts` states only the completed tensor shift
normalizations for arbitrary data satisfying the existing laws. It includes both
generator signs and both Roos-model equations. Its module is
`Sheaf.Paper.PodNormalizedTensorSignedShifts`; it has one hole.

`lem-pod-unrestricted-normalized-reconstruction` records the proved binder-free version
of the existing normalized reconstruction argument. It has no hole and is exposed in
the existing reconstruction module. Change record:
`coord/changes/Y6-normalized-reconstruction-generality.md`.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
