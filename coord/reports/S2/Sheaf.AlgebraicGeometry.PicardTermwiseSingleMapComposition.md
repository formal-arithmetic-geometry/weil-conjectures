## What changed

Restored `Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition` from its quarantine
archive and repaired its proof for the current source library. Removed the obsolete local
irreducibility attribute on `derivedPullback`, which is now an `irreducible_def` upstream.

Reused `perfectHomTensorCounit_comp` and the fixed tensor-comparison API from the proof-only
import `WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit`. This removes the private
`pinnedCounit`, `pinnedComposition`, and `counit_composition` duplicates and avoids repeated
kernel expansion of their large existential specifications. The remaining private helpers
prove the single-complex identity, the normalization of the public maps, and the naturality
calculation. The public theorem signature, public map definition, public imports, and
original docstrings are unchanged. The existing node's proof and dependencies now name the
reused source API. A theorem-scoped `cleanup.letToHave false` retains shared local
comparison data and avoids repeated cleanup traversal of the nested choices; all kernel
and delivery checks remain enabled. No source-library module is changed. The complete
repaired source compiled without errors or warnings in 46.6 seconds under the normal
60-second limit.

Change record: `coord/changes/S2-picard-termwise-composition-restore.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.picardTermwiseSingleMap_composition` is fully proved, retaining
node `lem-sc-picard-termwise-single-map-composition`. This is a compatibility repair of a
previously proved archive: zero existing holes, zero holes closed, zero holes added, and
zero statements split off. Every private helper is proved. No `sorry` remains in the module.

## No longer needed

No DAG node, module, or existing import is pruned. Both public imports remain necessary
for the public definition and theorem. The replaced private helpers have no separate DAG
nodes; their original composition theorem remains needed through the reused source API.
The blueprint unit and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The 2026-10-20 cluster restore reverted the module into quarantine. Its archived proof had
zero holes but failed against the current upstream irreducible `derivedPullback` because
of the redundant local attribute. After removing that attribute, repeated checking of the
nested composition choices also exceeded the normal per-file limit. The existing fixed
counit API supplies exactly the same factorization and avoids those duplicate definitions.
No mathematical statement error or additional flatness hypothesis was introduced.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
