# NU supported Cartier purity: stage-1 routing repair, 2026-10-24

The repair note released stage 1 but incorrectly set keep_plan=true. The live
node is unsplit, with empty proof/proof_deps and no Lean record. In
tools/dag_queue.py, keeps_plan intentionally allows a returned coarse split to
retain its statement path and proceed to stage 2. This item has no such split.
Consequently stage1() and stage2() both selected it; claim.py queue_stage chose
stage 2 (highest row) and delivery_stages.py chose stage 2 (last row). The
stage-1-only delivery e5f07abe70bb was then returned as an S2 delivery. Repeated
workers received an S2 brief and empty S2 sandbox, although the S1 candidate,
report, citation and search logs were intact.

Set only this repair note's keep_plan to false; preserve its released stage-1
state and the earlier finite-coefficient route decision. Add this explanation
and the saved S1 sandbox path to the repair note and preferred-upstream brief.
Remove only this item's S2 row from queue.tsv and queue.md (adjust counts).
The generated queue files already contained unrelated uncommitted updates;
the maintenance commit stages only this item's removal against HEAD, leaving
those other worktree updates untouched. Backups of all five changed/new files
are adjacent, ending .maint-NU-stage1-routing-20261024.bak (empty for a new file).

A fresh live Dag computation before repair selected the item at both S1 and S2;
changing just the flag in memory kept S1 and removed S2. Recompute from the
written note, verify claim.py selects S1, and validate the saved candidate with
the stage-1 no-push delivery tool. A future normal queue.py rewrite will use
the corrected source record, so the invalid duplicate will not be regenerated.
No mathematics, node statement, Lean file, launcher-owned code, review service,
landing tool, provider setting or concurrency policy is changed.
