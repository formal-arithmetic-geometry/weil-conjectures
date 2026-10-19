# Q10 section-colimits stage-1 recovery (2026-10-17)

The NI split was accepted at `a62f04c5d160f41810281571c1c6ed0ab37c65ca` (reviewer
NT-cc-NI-483244714, FIX), but shared promotion of the item remained pending.
The live node differed from the pre-delivery side node only by `lean_audit`.
`tools/nt_land_batch.py:promote` compares entire JSON records, so the added
none/empty audit was treated as a collision. The new helper had already
promoted, but the item stayed unsplit in the shared DAG used by queue.py.
The side node was split and reviewed, so unchanged stage-1 retries could
never satisfy delivery preflight. Failure counts were not the cause.

Recovered the existing reviewed split in the live repository at `54a89a671eeced35af60f791f19af4b193b03c6b`
under its merge lock. Copied only the eight fields changed by the accepted
split: status, proof, proof_deps, proof_origin, split_report, mathlib_searches,
reviewed, tool_uses. Preserved the live audit and every other field.
The recovered node equals the side node; the helper equals its accepted
version. Statements, mathematics and Lean files were not changed.

Retired the exact completed promotion journal
`local/stage1-batch/pending/a62f04c5d160f41810281571c1c6ed0ab37c65ca.json` after verifying the live
record. Regenerated queue.tsv, queue.md and blueprint-index.tsv with queue.py.
Every existing file changed or removed has an adjacent `.maint-Q10-local-transport-1792214641.bak` backup.
The Q10 claim is retained for the legitimate stage-2 assignment.

Validation: review_split.py PASS with SHEAF_DAG=dag/nodes; proof_deps is
exactly the union of proof-step uses; no new dependency cycles against the
pre-recovery graph; the live audit is preserved; the computed and written
queue contain this item only in stage 2. The relative-colimit-test helper
remains an ordinary open stage-1 task. No compiler or global build ran.

Next worker: stage 1 is complete. Use the stage-2 brief and stage-2 sandbox
for the legitimate statement task. The Q10 stage-1 sandbox is historical
and has no new split to push. The old Q102 stage-2 packet was returned and
archived; it is not an accepted Lean interface. Respect current statement
dependencies and current stage-2 validation. Do not manufacture a stage-1
edit to bypass the unchanged-item diagnostic.

Launcher follow-up (outside this maintenance edit authority): make shared
promotion merge disjoint split-owned and maintainer-owned metadata changes,
while rejecting real conflicts. Preserve audit updates and make replay
recognize an already promoted split plus newer metadata. Add a regression
case for a concurrent none/empty lean_audit addition. The dispatcher should
also recheck live stage-1 completion for held claims before relaunch and
retain the started stage when reaping a worker across a queue transition.
No launcher, review-service or landing-tool code was edited.
