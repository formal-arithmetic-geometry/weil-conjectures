# N0 compact-support coefficient-change cycle repair, 2026-10-21

The stage-1 packet for lem-fix-compact-support-coefficient-change repeatedly passed
the local delivery gates, then failed server preflight on the same pre-existing
18-node strongly connected component. Ordinary workers could not repair its
other existing nodes under their item-only scope.

35763188dc reassigned def-weil-derived-direct-image from SfDerivedDirectImage to
SfCommonStageDirectImage; 8ae757b401 added the latter's genuine proof prerequisites.
That made the foundational finite/integral definition depend on the later
common-stage adjunction, whose integral prerequisites use the foundational
definition. The finite/integral module was left with no owning DAG node.

Restore the foundational node's lean, proof, proof_deps, proof_origin and
reviewed_lean from before 35763188dc. Preserve its current statement and all
other blueprint/split data. Move the complete upper interface, proof,
dependencies and original review history verbatim into
def-weil-common-stage-derived-direct-image. Its statement describes the existing
landed declarations; no new theorem, proof, search or review is claimed.
Connect the actual common-stage/Weil consumer lem-dl-a1-weil-open-image-delta to
that record by an added reference and statement dependency. No Lean file changes.

A read-only candidate graph audit removed exactly the 18-node SCC and introduced
no cycle. Each of SfDerivedDirectImage and SfCommonStageDirectImage has exactly
one owner; all upper proof dependencies and review provenance are retained.
Other pre-existing global DAG findings are outside this repair. The item's
normal server delivery preflight must be rerun on the retained four-helper packet.

Existing changed files have adjacent .maint-N0-1792553752.bak backups. New files
have initial snapshots with that suffix. The next worker should retain its
four statement-only helpers, six-step assembly and searches, refresh current
main, and run the ordinary no-push dry run before delivering for review.
