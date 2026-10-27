# Q20 product-topology spectral uniqueness: pruned handoff repair

The delivery 3117c352a859821b8b5391055e6a23069c18a30a has a saved independent PASS with no fixes.
Its old landing refused eligibility, then misreported that refusal as an
unpromoted side completion. Both DAG paths are /home/ubuntu/weil-conjectures-sheaf/dag/nodes;
both completion predicates are false. There is no side completion to promote.

The authoritative progress walk excludes the item and both direct citers,
lem-trf-gauss-rational-function-stability and lem-trf-frobenius-root-coordinate-test.
The ordinary graph still reaches it (distance 4, queue cut
distance 4), but progress_open is false and stage1()
does not offer it. The current queue has no row for it. The human's progress
walk restriction is implemented by e927f8276ec (2026-10-25 01:36 +08).
Retained roots in coord/preopen.txt do not override that progress predicate.

Maintenance archived the exact approved packet at refs/superseded/Q20/lem-trf-product-topology-spectral-uniqueness/3117c352a859821b8b5391055e6a23069c18a30a, removed its stale
Q20 return and claim, and recorded a release for pruned work. No completion,
abandonment, parking, dispatch exclusion, delay or concurrency limit was added.
The DAG node remains unsplit and byte-for-byte unchanged. If a changed target
route makes it eligible again, ordinary dispatch remains available; recover the
approved work from the archive and recheck changed cited statements first.

Evidence, every changed file's .bak, original review and approved payload:
/home/ubuntu/weil-maint-bak/Q20-product-topology-spectral-uniqueness-1792875802/. The local review-service verdict is preserved as historical evidence.

Protected-tool follow-up (report only): tools/nt_land_batch.py must distinguish
an incomplete item excluded by progress/active reach from actual completion
divergence. Its notopen fallback currently infers side completion merely from an
incomplete queue node. Review/return handling should retire a genuinely pruned
handoff with an archived packet instead of prescribing worker proof edits.
No landing tool, review service or launcher-owned tool was modified.

Recorded 2026-10-24T21:21:53Z; maintenance objective: repair coordination data, without doing
the item's mathematics or reopening a plan the current targets do not require.
