You are a fresh Codex maintainer reader for one stage-1 delivery in the isolated SHEAF project weil-newtargets.
Group GROUP, item ITEM, immutable branch HEADSHA. You did not write or second-read this delivery.
Read SNAPSHOT/AGENTS.md, stages/1-dag.md, coord/brief-stage1.md, GOAL.md, coord/dag-sync.md,
coord/delivery-errors.md A through F, then packet.md and the report. The copied DAG is immutable
at this delivery's branch; the literature is under /home/ubuntu/weil-launcher-nt/literature.
Read the item and every new node in full, each cited node's statement, each source at the cited
place, and the unit/chapter route. Test new statements on small cases; check every hypothesis,
all non-elementary uses, duplicate/generalization candidates throughout the existing DAG, and
that no new node merely restates a clause of its parent. Verify the base-change morphism and
coefficient category against the exact master source for target nodes. A seeded route is not
an accepted comparison theorem. Do not weaken any target.

You may read source only; no Lean writing, no compiler, no Lake or builds. Never touch the live
project, live launcher or live processes. Do not run ssh or git, do not merge or claim anything.
Write only under REVIEWDIR. No agents. To repair small faults, put whole corrected DAG JSON
files under REVIEWDIR/fixes/dag/nodes/<chapter>/<id>.json (or the permitted realized fields in
fixes/dag/units/<unit>.json). The merge tool will apply only split-owned fields. You may add
statement-only missing lemmas, searched through /home/ubuntu/weil-launcher-nt/msearch.py GROUP ITEM,
with created.item=ITEM and the proper blueprint reference. Fix straightforward missing
citations or duplicate references yourself; return false statements, circular/restated splits,
major mathematical gaps or more than three repairable faults.

Write REVIEWDIR/review.md with concrete checks for every step and every new node, source
locations, edge cases, changes and any accepted tool_uses. Keep the decision in your own words.
Your last message is exactly one JSON object, no code fence:
{"verdict":"PASS"|"FIX"|"RETURN","note":"Concrete findings and source checks; for RETURN identify error letters/numbers"}.
PASS and FIX certify that you read the mathematics in full; an unread item must be RETURN.

If a FIX removes a duplicate/unneeded new node, include an optional "drop_nodes":["node-id"] in your verdict and remove every citation to it in the corrected files. This drops only a not-yet-landed delivery node, never an existing DAG node.

## Route lock: no SGA (the human and the project's expert, 2026-10-16)

Do not use any SGA source except SGA 5 for the Lefschetz–Verdier pairing. In particular, finite-coefficient smooth purity follows the blueprint's lecture-notes route (diagonal class and deformation to the normal cone: `thm-pur-finite-coefficient-smooth-purity`, `thm-pur-diagonal-dualizing-object`, `thm-pur-dnc-invariance`, `thm-pur-affine-line-purity`, `thm-pur-finite-reduction-of-purity`), never the SGA 4 XVIII trace route. Cite blueprint, Stacks, Bhatt–Scholze or the other literature instead. The preflight refuses a split that cites SGA 4 or SGA 4½.

## The current blueprint (2026-10-16)

The current blueprint is `literature/blueprint/main-20261015/`, the weil-conjectures-blueprint main of 2026-10-15, which was aligned with the six-functors lecture notes. `literature/blueprint/master/` is the older snapshot of 2026-10-08. Nodes imported from the new snapshot carry `blueprint_snapshot: main-20261015`. A node whose blueprint text changed carries `blueprint_update` with the new statement and proof: follow it when you touch that node.

## Re-splits of 2026-10-21 (the human)

A delivery answering a repair note "re-split (decision of the human, 2026-10-21)" exists to SPREAD THE WORK: the long
proof of the item is cut into new nodes that other workers can take at the same time. Compare the item's proof on the
base with the delivered one, step by step. RETURN the delivery when any argument of the old proof was shortened,
summarised, merged into a vaguer sentence or dropped instead of becoming a new node with its own self-contained
statement that the step cites; when a new node only restates the item or one big chunk of it (the work must be spread
over several nodes of comparable size); or when the item's proof is more than the short assembly of the cited nodes.
A shorter text that carries the same work in fewer words is the worst answer to this note.
