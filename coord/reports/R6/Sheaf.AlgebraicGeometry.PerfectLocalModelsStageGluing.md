## What changed

Restored Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing from the quarantine
path in coord/rework.tsv. Replaced its public import of the withdrawn
Sheaf.AlgebraicGeometry.DerivedPullback by
WeilConjectures.AlgebraicGeometry.DerivedPullback. Replaced the private retired
Sheaf.Paper.DerivedHomMayerVietoris wrapper by its source-library module.
Explicitly disabled automatic implicit binders. No theorem signature, definition,
proof route or DAG attachment changed. The public theorem
signature and proof body match the archived source byte for byte. The restored
file compiles cleanly (25.6 seconds), within the unchanged file limit.
The additional ordered compile produced complete compiled artifacts for the
unchanged quarantined direct parent PerfectLocalModelsEventuallyCompatible
against this restored module; its temporary test source is excluded from delivery.

The preserved argument obtains the stage object and compatible local comparisons
from perfect_local_models_stage_comparisons, glues their homs using
derived_hom_mayer_vietoris, and transports local invertibility through the
open-site equivalence. The two cover arguments provide pointwise witnesses.
This works for empty schemes, empty overlaps and equal opens without an extra
nonemptiness assumption. The unit route is unchanged.

Change record: coord/changes/PerfectLocalModelsStageGluing-restoration.md.

## Proved and sorry left

This is a zero-hole rework restoration. Holes closed: 0 of 0. Holes added: 0.
No sorry remains in the item. The public theorem
AlgebraicGeometry.perfect_local_models_stage_gluing and the proved private helpers
isIso_schemeRestriction_of_isIso_localized and
model_witnesses_of_local_comparisons retain complete proofs. No lemma is split off.

## No longer needed

Removed imports: Sheaf.AlgebraicGeometry.DerivedPullback (withdrawn empty module)
and Sheaf.Paper.DerivedHomMayerVietoris (retired re-export wrapper), replacing both
with their current source-library modules. No mathematical dependency, node or
module is pruned. In particular stage comparisons, derived Hom Mayer–Vietoris,
and the open-restriction definitions all remain needed. The quarantined parent
PerfectLocalModelsEventuallyCompatible remains needed and is not withdrawn.

Searches through leanfinder, loogle, the supplied grep service and local sources
found the generic isomorphism-transport lemma and ordinary sheaf gluing, but no
shorter independent derived stage-gluing theorem.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because of the recorded cluster-restore quarantine,
not because its mathematics was withdrawn. Its archive has zero holes and already
contains the planned proof. The stale public pullback import names a module that
has since been emptied; the repair imports the current source implementation
directly. The archive compiles against today's repaired dependency build, so this
is import migration and restoration, not a claim of newly closing a proof hole.
The current DAG proof remains accurate and needs no node edits. The current
blueprint places the former semicontinuity unit text under
sk-thm-picard-perfect; no unit or blueprint text is edited.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
