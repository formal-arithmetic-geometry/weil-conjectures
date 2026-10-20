## What changed

Retire `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations`, as listed in the stage-3 queue.
Its theorem `AlgebraicGeometry.finitePresentation_local_maps_eventual_overlap_equations`
is already proved in `WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations`. The source theorem omits only the unused
Noetherian-ring assumption and otherwise has the same hypotheses and conclusion.
Redirect the sole direct consumer, `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`, by changing its private proof
import. Its declaration signatures, public imports and proof bodies are unchanged.
Update the existing node's Lean attachment to the source theorem. Withdrawal follows
`deleted.txt`; no file or declaration under `lean/WeilConjectures/` is modified.

Validation: the adapted consumer compiled cleanly through `lcompile.py` in 6.2 seconds.
`import_direction.py may` confirmed that the replacement import introduces no cycle.
A textual signature comparison found exactly one difference: the source theorem drops
`[∀ k : I, IsNoetherianRing (R.obj k)]`. The consumer has no proof-body edits.
The source of Stacks Tag 01ZR was checked at
`literature/stacks-project/limits.tex:2548` (in particular the first proof at 2582–2589).
Its affine transition and quasi-compact/quasi-separated assumptions do not impose
Noetherianity. Local searches found the adopted theorem and its sole direct consumer;
LeanFinder returned general gluing lemmas, while Loogle and the Mathlib grep had no
exact match. No new theorem is needed.

Change record: `coord/changes/retire-finite-presentation-local-map-overlap-equations.md`.

## Proved and sorry left

The assigned module started with 0 holes and leaves 0 holes. No hole is closed or
added; this is retirement of a duplicate, not new proof work. The replacement theorem
is already proved by finite-pair compatibility and a common upper bound. Its proof
continues to use the existing declared pair-compatibility dependencies.
The adapted consumer also has no `sorry`. No new modules or nodes are introduced.

## No longer needed

Withdraw `lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalMapOverlapEquations.lean`.
The consumer no longer imports `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` and instead imports its adopted source
counterpart. The duplicate private helpers `finiteCommonStage`,
`tensorPullbackProperties`, `restrictionComponent`, `composeDescentComponents` and
`assocFive` disappear with the withdrawn module; their source counterparts remain.
The node `lem-pc-fp-local-map-overlap-equations` is retained and redirected.
Its proof dependencies `lem-pc-fp-local-map-pair-eventually` and
`def-pc-local-map-pair-compatibility` remain needed by the adopted source proof.
No other module or node is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described a module with holes or a definition repair;
the current queue instead explicitly requests retirement (`retire`, one consumer).
The module already has a complete proof, and the upstream version is more general.
The node's old Lean attachment still pointed at the duplicate. Its mathematical
statement and proof plan remain valid; only that attachment needs redirecting.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
