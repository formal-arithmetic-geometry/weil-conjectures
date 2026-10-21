# Q135 maintenance: finite-free strict tower transport

The repeated H2 repair failed because the returned brief required moving shared definitions
out of a downstream module containing completed proofs. The stage-2 packet validator admits
existing dependency nodes only within the item's prerequisite closure and requires theorem
proofs in delivered modules to be `sorry`. The required consumer is outside that closure.
Changing its dependency relation or erasing completed proofs would be wrong. This was a
maintenance relocation, not an ordinary statement delivery.

The repair extracts the existing `SheafOfModules.projectionPost` abbrev and
`SheafOfModules.StrictProjectionLimitData` structure verbatim into
`lean/Sheaf/CategoryTheory/StrictProjectionLimitData.lean`. The original module
`lean/Sheaf/Paper/RingedStrictTowerProjectionMorphism.lean` publicly imports it and otherwise
is byte-for-byte the original source with those two declarations removed. In particular its
completed proofs and public theorem signature are preserved. The owning definition node
`def-sbc-strict-projection-tower-data` landed concurrently; reuse it, without creating the
suggested duplicate `def-weil-pbc-strict-projection-limit-data` node.

The global build captured the extraction in e2474ee0c0d. It also captured experimental
compiler edits while this maintenance was in progress; the build's restoration commits
b87061b6de5 and 67829795252 removed those edits. The final source was checked against the
original snapshot: only the extraction and public import remain. All experiments are
retained as .bak files; they are not the final repair.

The worker rebased on that extraction, delivered 188e5deb1f73, and independent review
NT-stage2-cc-188e5deb1 accepted it. Server commit 85c9242b8337 merged the item and removed its
return. The statement now cites the existing definition owner. No consumer module needs
to be included in another worker delivery. Both extraction and item merge are ancestors of
verified main cb438c06d529 (green build at 2026-10-21 15:40:41 UTC).

Validation used tools/lean_file.sh, one file at a time with the unchanged 60 s limit:
the extracted owner compiled in 2.4 s and the merged item in 13.7 s. The unchanged original
consumer and the final consumer each timed out at 60 s; this pre-existing independent
compiler concern is not a successful compile claim. It no longer blocks the item's
statement-only delivery. The shared build later reported green. No lake build was invoked
by this maintenance, no unrelated process was stopped, and no launcher, review, landing,
or admission tool was changed.

This maintenance commit corrects the extracted module's blueprint docstrings to the actual
existing owner and updates that node's informational lean.note to explain the public
re-export. Every modified file has a .bak. This report is a maintenance record, not a
request to merge or dispatch an item already accepted. If a future H2 return requires a
similar proved downstream relocation, perform the maintenance extraction first; changing
the landing validator is launcher-owned and must be escalated rather than edited here.
