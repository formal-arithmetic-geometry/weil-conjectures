## What changed

Proved `AlgebraicGeometry.Scheme.pbcQbarIdempotentComplete` in
`Sheaf.Paper.PbcQbarIdempotentComplete`, preserving its complete signature.
For every finite intermediate field, apply `finite_stage_karoubian` to its canonical
small model `pbcFiniteField`; the resulting raw rational category is definitionally
`pbcStageCategory`. Apply `pbcFilteredRetractDescent` to these instances, then use the
existing Karoubi full, faithful, equivalence and triangulated-functor instances.
This realizes the blueprint argument without any new statement or construction.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.pbcQbarIdempotentComplete`
(node `thm-weil-pbc-qbar-idempotent-complete`). The item has zero holes left.
Added zero holes and split off zero statements. The proof uses the already stated
`AlgebraicGeometry.Scheme.finite_stage_karoubian` and
`AlgebraicGeometry.Scheme.pbcFilteredRetractDescent`; their existing holes are unchanged.

## No longer needed

Removed proof imports `Sheaf.Paper.IntrinsicQbarCategory`,
`Sheaf.Paper.FiniteStagePairCategory`, and `Sheaf.Paper.PbcVerdierAxioms`.
The intrinsic category is unused: the assigned theorem concerns the published
`pbcQbarCategory`, definitionally the existing `PbcFiniteStagePairCategory`.
The latter two imports are redundant because `PbcQbarCategory` already publicly
imports their modules; their statements and structures remain needed transitively.
No planned mathematical dependency is bypassed, and no DAG node is withdrawn.
No quasi-inverse implementation or additional equivalence lemma is needed:
Mathlib's `toKaroubi_isEquivalence` already implements the splitting argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the proof plan was needed to close the assigned theorem.
The Qbar-definition node now records `intrinsicPbcQbarCategory`, whereas this older
item's unchanged signature still explicitly names `pbcQbarCategory`. This delivery
proves exactly the assigned legacy signature; it does not silently assert a comparison
with the intrinsic category. The unrelated intrinsic proof import is removed.
The current blueprint proof in `main-20261015`, order 1895, has the same argument
as the module's older source reference. Its finite-stage and descent steps are retained.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
