## What changed

Proved `AlgebraicGeometry.ProEtale.properHeartContinuityDirectImage` in
`Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage`, with its statement and
visibility unchanged. The filtered-colimit clause applies the existing bounded-complex
continuity theorem to degree-zero complexes and uses `colimit.post_post`.

A fully proved private helper `ringDerivedDirectImage_additive` restricts the derived unit
to K-injectives. The restricted localization is full and essentially surjective using the
existing arbitrary-quasi-isomorphism resolution theorem. The unit identifies its composite
with the derived direct image with an additive functor. Additivity descends through the
localization. The source-library finite-subsum theorem then proves the arbitrary direct-sum
clause, including the empty family. No bounded or monomorphic resolution hypothesis is added.
The original declaration docstring is retained; the node now records the actual Lean argument.

The proof uses explicit non-public imports of `Mathlib.Algebra.Homology.HomologicalComplexLimits`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`,
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, and
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset`.
The existing derived-unit interface is retained as an explicit proof import. Updated the
existing node's proof, proof dependencies and proof origin.
No public interface, definitions, instances, target signatures or consumer modules changed.
On resumption, the retained module was compared with current shared sources and recompiled
through `lcompile.py` in 4.4 seconds without errors or warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.properHeartContinuityDirectImage`
(node `det-proper-heart-continuity-direct-image`).
Added 0 holes; split off 0 theorems. The private helper is proved completely.
There are 0 textual `sorry`s left in the delivered module and no new modules.
The proof uses the existing named declarations `boundedContinuityDirectImage`,
`ringModuleDirectImage_hasKInjectiveResolutions`, and
`rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso`; those existing dependencies remain
work for their own items. This is a local proof from the declared dependency interfaces,
not a claim that the target closure is now axiom-free.

## No longer needed

Removed the following proof imports and direct proof dependencies:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`
  (`lem-sc-bounded-below-injective-resolution`): the published arbitrary K-injective
  resolution interface in `ProEtaleBoundedContinuityDirectImage` suffices.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  and its source-library counterpart
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`lem-weil-pbc-module-sheaves-colimits-forgetful`): Mathlib's colimit instances and
  single-complex preservation give the required categorical comparisons directly.
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
  (`det-pe-topos-functoriality-inverse-image`): additivity of the actual underived direct
  image is already proved in `ProEtaleBoundedContinuityDirectImage`; its derived unit
  gives the finite-sum calculation without the separate topos-functoriality theorem.

Removed those three obsolete top-level `tool_uses` approvals from the node. These are
removals from this theorem's direct proof route; other items may still need the modules.
The existing abstract-derived-category and colimit convention dependencies remain.

The retained attempt's unpublished helper file
`lean/Sheaf/AlgebraicGeometry/ProperHeartContinuityDirectImageDirectSums.lean` was removed
from the sandbox, together with its temporary import: its sole hole is fully handled by
the finite-subsum argument inside the original theorem. It never existed in the shared
repository, so no withdrawal or new node is required.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had a valid filtered-continuity argument but left the entire direct-sum
clause in a new holed helper without a node or report. This delivery retains that first
argument and completes the second clause, with no split-offs. Its `letI` style warning was
also removed.

The original plan's explicit finite sums of chosen bounded resolutions are unnecessary:
additivity transports across the invertible derived unit on K-injectives, and the existing
source-library finite-subsum theorem assembles arbitrary coproducts. This is the same
unit-prescribed finite-subsum route. No mathematical defect of the statement was found.
Edge cases are covered uniformly: all integer degrees, arbitrary ring sheaves (including
the zero ring), non-monomorphic resolution maps, and empty coproducts. No extra hypotheses
or special choices of a derived-category model were introduced.

The previous attempt completed the proof but its delivery never reached preflight because
temporary-worktree checkout timed out and the retry remained queued. This session started
with the required unmodified dry run, retained the proof and node edits, checked the current
source interfaces and unit route, and successfully recompiled the delivered module. No
launcher scripts or shared-repository files were edited.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
