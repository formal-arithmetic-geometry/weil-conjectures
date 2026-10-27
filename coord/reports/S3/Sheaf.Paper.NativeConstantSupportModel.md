## What changed

Filled three theorem proofs in `lean/Sheaf/Paper/NativeConstantSupportModel.lean`.
`towerConstantRestriction_exact` reflects finite limits and colimits through
`SheafOfModules.toSheaf`, since restriction leaves the underlying abelian sheaf
unchanged, then applies pointwise preservation on the strict diagram category.
`systemRestriction_exact` composes the existing exact coefficient-sequence
restriction with this exact constant restriction; both factors are additive.
`ordinaryReduction_additive_data` uses additivity of restriction and inverse
limit, then transports additivity to the left adjoint using the actual
`ordinaryReductionAdj` adjunction.

All declaration signatures, definitions, docstrings, visibility and imports are
unchanged. The existing mathematical route is unchanged; no node update or
change record is required. No consumer adaptations are necessary.

## Proved and sorry left

Closed three of the original nine holes, with no new holes:

- `WeilConjectures.PurStrictScalar.towerConstantRestriction_exact`.
- `WeilConjectures.PurStrictScalar.systemRestriction_exact`.
- `WeilConjectures.PurStrictScalar.ordinaryReduction_additive_data`.

Six original holes remain, all attached to
`def-pur-native-constant-support-model` and retaining their source and complete
proof descriptions in their existing docstrings:

- `WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique`.
- `WeilConjectures.PurStrictScalar.systemProper_existsUnique`.
- `WeilConjectures.PurStrictScalar.systemPullMap_isIso`.
- `WeilConjectures.PurStrictScalar.systemOpenMap_isIso`.
- `WeilConjectures.PurStrictScalar.ordinaryLimit_rightAdjoint`.
- `WeilConjectures.PurStrictScalar.reductionRightComparison_existsUnique`.

These are untouched original holes, not split-off statements. The completed
proofs use the existing library and Mathlib declarations directly. No axiom,
new theorem statement, definition repair or decomposition is introduced.

## No longer needed

None. All four original public imports remain needed by the public definitions
and theorem statements. There are no proof-only imports to remove, no new
modules, and no pruned nodes. The node has no planned proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The item node is a definition node with
empty `proof` and `proof_deps`; the nine accompanying theorem docstrings provide
the arguments. The three completed proofs implement those arguments directly.
There is no current return or rework entry for this item.

Searches: `msearch.py` LeanFinder found the actual sheaf restriction functor,
its additive instance and the forgetful finite-limit instances; Loogle found
`CategoryTheory.Adjunction.left_adjoint_additive`; grep and direct `rg` located
pointwise whiskering preservation and the proved
`coefficientSequenceRestriction_exact` API. Existing general sequence-projection
adjunction machinery was inspected, but is not imported: the remaining
normalization and inverse-limit identifications are not established by these
three proofs.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
