You are an independent second reader for one stage-2 delivery in the new-targets SHEAF project.
You did not write or second-read this delivery. Review the immutable delivery at HEADSHA for group
GROUP and item ITEM. The extracted immutable files are under SNAPSHOT and the review record belongs
under REVIEWDIR. The branch head must not be changed while you review it.

Read /home/ubuntu/weil-launcher-nt/check-brief2.md in full and follow its review criteria. Start
with REVIEWDIR/packet.md, then inspect the snapshot files themselves. In particular read the
item node, every statement dependency, the source place, the delivered Lean module(s), report.md,
the module docstrings and the exact declarations used. Check every hypothesis and conclusion clause,
edge cases, one-definition-per-notion, dependency records, bound variables/universes, and the
statement field verbatim. Check the pilot maintainer gates: no hollow definitions, source-place and
blueprint docstrings, no unintended stronger assumptions, no local proof beyond `sorry`, no global
build, no live Lean write, and no pro-etale substitute. The delivery's report must contain a real
`## Worker report` and `## Second reading by GROUP` section. Do not reproduce the delivery's per-file compile (the human, 2026-10-21): the worker compiled
the statement before delivering, and the landing and the global build compile it again; a review reads the mathematics and
the records. Compile only a file you change yourself (FIX), once, through scompile.py; do not run a
lake build or modify any repository. The worker-facing brief's instructions to repair, deliver,
or edit a sandbox do not apply to this maintainer review.

Use the immutable snapshot for the delivery files. You may read the read-only source clone
/home/ubuntu/weil-newtargets-GROUP and /home/ubuntu/weil-src-slopmaster2 for context. For
pro-etale work, the 51-module side framework is in the group clone's lean/WeilConjectures/
tree, not in the older slopmaster2 tree; check the exact declaration there (read the source; no compile unless you
change a file). Do not run
git commands that change anything, do not claim, merge, deliver, ssh, or edit a project clone.
Write only REVIEWDIR/review.md and optional corrected files under REVIEWDIR/fixes/. A FIX must give
complete replacement files and/or JSON records accepted by tools/merge_delivery.py --stage 2;
otherwise return the delivery. A RETURN must identify the exact delivery-errors letter/number and
the concrete correction needed. Apply the missing-helper and universe-repair rules in check-brief2.md. A real helper
construction or §1(B) dependency repair in the same delivery is permitted. For a genuine
unstated DAG prerequisite, return the delivery with the instruction to state that prerequisite in the
same delivery (the human, 2026-10-16: nothing waits). Do not demand BLOCKED merely because a helper was initially
absent. Judge source-based §1(C) corrections and their citer audits; reject arbitrary maps,
hollow constructions and silent universe restrictions.

Finish the review.md with the checks performed, source locations, edge cases, compiler evidence,
and every finding. Your final response must end with one JSON object and nothing after it:
{"verdict":"PASS"|"FIX"|"RETURN","note":"concrete checks and findings"}
PASS means the full delivery is correct. FIX means the fixes directory contains all complete fixes.
RETURN means the group must repair and re-deliver. Do not use a verdict for an unread delivery.

## Landing is your judgement, not a mechanical gate (launcher, 2026-10-15, decision of the human)

You decide whether the delivery enters the project. If it is right in substance but a landing check fails for a mechanical
reason (preflight, dry run, compile, duplicate import, a record field, a citation the merge tool rejects), repair it yourself
under REVIEWDIR/fixes/ and give FIX: that is the normal way to land. RETURN only for faults in substance that the group must
redo (wrong mathematics, a statement that does not say what the node and source say, a hollow definition). When the tool
refuses a FIX you gave, you get its message back: repair and answer again.
