# NR maintenance: lem-sfb-grothendieck-sheafification

The repeated failures came from inconsistent stage-1 eligibility, followed by a contradictory return. They were not provider errors or a mathematical defect.

The live `coord/repair-notes/lem-sfb-grothendieck-sheafification.json` deliberately reopens the item for the human's 2026-10-21 re-split. Commit `0629838df06` explicitly makes `stage1_completed()` false while that note is released, even if Lean is closed. However, `Dag.stage1()` still tested `unfolded()`, which returns true for the closed Lean module. The same node was therefore claimable and passed the required re-split preflight, but was absent from the stage-1 queue that landing checks.

Before maintenance, the server reported: `repair_owed=True`, `finished=True`, `unfolded=True`, `stage1_completed=False`, stage-1 distance 3, and `stage1_listed=False`. The retained split has five assembly steps totaling 1761 characters and one new statement-only node, `lem-sfb-presentable-generator-cardinal-bound`. Four pushes (`514560f10e4`, `5f255325509`, `b61fd68d3a9`, `efd4316e21c`) were returned despite affirmative mathematical reviews. Subsequent workers correctly refused to invent mathematical changes to satisfy the A6/A7/B10 supersession return, and repeatedly obtained passing dry runs instead. The 2026-10-21 09:14 UTC return incorrectly treated the earlier human instruction as cancelled by P1's 06:16 proof landing; the explicit re-split override and route note say otherwise.

## Changes

Server project: `/home/ubuntu/weil-conjectures-sheaf`, branch `sheaf-dag`.

- Commit `243a4db5baf`: `tools/dag_queue.py` now uses `stage1_completed()` when selecting direct and statement-downstream stage-1 work. Closed nodes with a released stage-1 repair are no longer discarded by the statement-downstream walk. The existing reach and ordering rules remain in force.
- The same commit adds `tools/test_stage1_repair_queue.py`, with six regression cases for closed repairs, statement dependencies, note resolution, unrelated nodes, stage isolation, and ordinary split/unsplit behavior.
- The item's entry in `coord/returns/NR.md` was corrected to withdraw the contradictory supersession objection and give the next worker the actual repair instructions. The original entry is preserved in a `.bak` file.

Only the project queue tool and coordination records were repaired. No launcher-owned scripts, review service, landing tools, concurrency settings, mathematical node, or Lean source were edited. No Lean compilation or `lake build` was run, and no other agent's processes were killed.

## Validation

The six new tests were first run against the original queue code: three failed, reproducing the omission of closed repairs. After the fix, all six passed. The existing claim-stage tests (16) and queue-order tests (2) also passed: 24 tests total. `git diff --check` passed. A fresh live-DAG query now reports `stage1_listed=True` for the item while `repair_owed=True`, `finished=True`, and `stage1_completed=False`; this is the eligibility guard read by the unchanged landing tool.

## Backups and commit discipline

Backups are on the server under `/home/ubuntu/weil-maint-bak/NR-grothendieck-1792579290/`, using `.bak` suffixes. New files have empty `.bak` placeholders and a manifest recording their prior absence. Every server commit is made under `coord/.merge.lock` with `SHEAF_LEAD=L-only`, author name `Bin Wu`, and email `844524296@qq.com`, committing only the maintenance paths so unrelated concurrent changes are excluded.

## Next worker

The human's re-split remains required. Reuse the retained sandbox, all authentic searches and citations, and the accepted mathematical split; do not redo the item's mathematics or claim an attachment in place of the re-split. Read the corrected live return and this maintenance report, refresh the sandbox's maintainer-owned fields from current main, run the required dry run, then push once through the normal delivery command. The earlier supersession objection was withdrawn because its tool/record cause has been repaired. The existing branch is `deliver/NR/lem-sfb-grothendieck-sheafification` at `efd4316e21c0bcae2efbe4aafa7ebc6270631b32`.

Keep the completed Lean interface and P1 proof landing `20261021T061607-L-1797094`. The repair note stays released until the normal stage-1 landing resolves it. The next delivery still requires its ordinary independent review and checks. No new mathematical review or delivery approval is claimed by this maintenance task.
