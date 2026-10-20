## What changed

Closed three existing proofs in `Sheaf.Paper.WeilTensorProduct` while preserving every
statement and definition signature. The first-variable K-flat tensor comparison uses the
site descent and K-flat resolution interfaces. Pullback preserves intrinsic completeness
by the completion unit square, and the rational tensor pullback comparison is constructed
from completion naturality, canonical tensor pullback, scalar localization, and tensor
induction. The Frobenius isomorphism also now supplies its two inverse laws explicitly;
its hom and inv fields are unchanged. The proof-only change is recorded in
`coord/changes/wfTensorFrobenius-explicit-laws.md`.

## Proved and sorry left

Closed three of the original ten holes:

- `SheafOfModules.wfSiteDerivedTensor_first`.
- `AlgebraicGeometry.Scheme.wfIsoPullback_complete`.
- `AlgebraicGeometry.Scheme.wfRationalTensorPullback_exists`.

Seven original holes remain, all in node `def-wf-tensor-product`:

- `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists`.
- `AlgebraicGeometry.Scheme.wfRationalTensorHom_exists`.
- `AlgebraicGeometry.Scheme.wfPullbackCompletion_exists`.
- `AlgebraicGeometry.Scheme.wfCompletePullback_linear`.
- `AlgebraicGeometry.Scheme.wfConstructible_complete`.
- `AlgebraicGeometry.Scheme.wfConstructibleInclusion_exists`.
- `AlgebraicGeometry.Scheme.wfConstructiblePullback_obj`.

No holes were added or split off.

## No longer needed

No imports or target-reachable nodes were pruned. The proof uses the K-flat resolution,
site-derived-tensor descent, intrinsic-completion reflector, canonical tensor pullback,
scalar localization, and the concrete sheaf tensor declarations recorded in the node.

## Where the brief, the DAG or earlier work was wrong

The module source had a quarantined rational-transport import that is absent from the
current live source tree; this delivery removes that unused import and retains the
constructible-inclusion proofs as their existing named holes. The three completed proofs
follow the existing node statements and do not add hypotheses or alter the unit route.
The explicit Frobenius inverse-law fields are propositionally forced by the component
isomorphism laws and do not change its mathematical data.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
