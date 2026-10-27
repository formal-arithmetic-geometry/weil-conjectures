## What changed

Proved `WeilConjectures.IntegralOnSlice.ordinaryCompletedCoverDetection` with its original
signature. Private helpers identify each ordinary pullback with actual module restriction,
using the existing completed coefficient restriction isomorphism, its finite projections,
and the site adjunction. Mathlib's cover-local criterion and the conservative underlying
abelian sheaf functor then prove joint reflection. Added proof imports of
`Sheaf.Paper.CompletedCoefficientRingedCoherence` (with `all` for its proved internal
restriction construction) and `Mathlib.CategoryTheory.Sites.LocalProperties`.
No interface or shared file changed.

Searches: LeanFinder returned general conservative sheaf functors and dense-subsite
comparisons, but no completed-coefficient result. Loogle did not recognize the local
`Sheaf.isIso_of_coversTop` identifier. Local Mathlib/source searches located that exact
theorem and `SheafOfModules.pushforwardPushforwardAdj`; their signatures were read and
used directly. The current blueprint unit was checked, and the new proof import passes
`tools/import_direction.py may`.

Validation: the item compiled remotely with exit code 0 in 15.7 seconds, without
warnings. Its public theorem statement and existing public imports are unchanged.
The item contains zero `sorry` tokens; only its own node’s `proof`, `proof_deps`
and `proof_origin` fields changed.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralOnSlice.ordinaryCompletedCoverDetection`
(node `lem-fix-ordinary-completed-cover-detection`). No holes remain and none were added.
All private helpers are proved. This is a proof, not a decomposition.

## No longer needed

The planned dependency `lem-fix-qcqs-ordinary-restriction-models`
(module `Sheaf.Paper.QcqsOrdinaryRestrictionModels`) is unused and removed from this node's
proof dependencies. Neither its strict quotient tower and Roos comparisons nor its exactness
input are needed to identify weakly etale restriction. No existing import was removed;
the item's public imports remain unchanged. All other planned dependencies remain used.
This does not withdraw the unused module or assert that its other consumers disappear.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cited the much larger quotient-tower/Roos restriction package for
an ordinary module-sheaf detection theorem. The completed coefficient ring restriction
isomorphism and the generic module adjunction suffice. The theorem's qcqs and nonempty
hypotheses are retained verbatim, though the restriction-and-cover proof does not need them.
No unit route is bypassed: this node's unit has no prescribed realized steps.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
