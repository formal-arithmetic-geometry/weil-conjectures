# Returns to group C

Written by the maintainer (`tools/merge_delivery.py return`): deliveries of group C that did not pass, with the reasons. One entry per return, newest last; an entry is deleted when the repaired delivery is merged. The claim of a returned item stays with C; its branch `deliver/C/<item>` stays until C pushes the repaired delivery to it.

## prop-weil-pbc-p1-acyclicity (2026-10-09 14:40 UTC, no branch)

Not a rejection: this item was already split and reviewed by L (commit 747ab27) when C claimed it from a stale `coord/queue.tsv`. L released C's claim; drop the item. `tools/claim.py next` now skips nodes that are already split and reviewed, so this cannot recur.

## def-weil-pbc-generating-sections (2026-10-09 15:06 UTC, branch head daefcff9)

The branch has no report file coord/reports/C/def-weil-pbc-generating-sections.md with the heading '## Review by C' (roles/remote-lead.md: one commit per item touching the item's node, its new nodes, the unit's realized fields and the report). Add the report (the worker's §6 report and your review) to the same commit (amend or squash), push to deliver/C/def-weil-pbc-generating-sections again (force-push of the delivery branch is fine), and L merges.

## lem-sc-c5 (2026-10-09 15:08 UTC, branch head 5d490bf7)

The branch deliver/C/lem-sc-c5 contains the commit of def-weil-pbc-generating-sections as well (it was branched from that delivery, not from sheaf-dag), so it changes a file outside this item's files; and, as for the first delivery, there is no report file coord/reports/C/lem-sc-c5.md with '## Review by C'. Each delivery branch must start from sheaf-dag (pull it first), contain one commit for its item (node file + new nodes + unit realized fields + the report), and be pushed to deliver/C/<item>. Rebase onto sheaf-dag, add the report, force-push both branches.

## lem-sc-c2 (2026-10-09 15:10 UTC, branch head 97a184ec)

The branch is the same stacked line as deliver/C/def-weil-pbc-generating-sections and deliver/C/lem-sc-c5 (four commits for four items, branches lem-sc-c2 and lem-sc-c4 pointing at one head), so it touches files of other items and has more than one commit. Please read coord/returns/C.md: each item needs its own branch starting from sheaf-dag, with exactly one commit touching only that item's node, its new nodes, the unit's realized fields and coord/reports/C/<item>.md containing '## Review by C' (lem-sc-c2 has a report; def-weil-pbc-generating-sections, lem-sc-c5 and lem-sc-c4 have none). Rebuild the four branches (cherry-pick each item's commit onto sheaf-dag, add the missing reports, force-push); L merges each independently.

## lem-sc-c4 (2026-10-09 15:10 UTC, branch head 97a184ec)

The branch is the same stacked line as deliver/C/def-weil-pbc-generating-sections and deliver/C/lem-sc-c5 (four commits for four items, branches lem-sc-c2 and lem-sc-c4 pointing at one head), so it touches files of other items and has more than one commit. Please read coord/returns/C.md: each item needs its own branch starting from sheaf-dag, with exactly one commit touching only that item's node, its new nodes, the unit's realized fields and coord/reports/C/<item>.md containing '## Review by C' (lem-sc-c2 has a report; def-weil-pbc-generating-sections, lem-sc-c5 and lem-sc-c4 have none). Rebuild the four branches (cherry-pick each item's commit onto sheaf-dag, add the missing reports, force-push); L merges each independently.

## lem-weil-pbc-module-sheaf-colimit-constructible (2026-10-09 16:03 UTC, branch head cef75684)

review_split.py FAIL: the item node has no split_report (required by stages/1-dag.md for a split item); otherwise the delivery is well formed (one commit, report with Review by C, one new node lem-weil-pbc-constructible-generation). Add the split_report and re-push the branch with one commit.

## lem-weil-pbc-finite-locally-free-degree-locally-constant (2026-10-09 16:06 UTC, branch head 15f83678)

the branch is stacked on the delivery of lem-weil-pbc-injective-resolution-ses (its commit range touches coord/reports/C/lem-weil-pbc-injective-resolution-ses.md): rebase the one commit of this item onto the current sheaf-dag tip so the branch contains only this item's node, its new nodes and its report, and re-push.

## lem-weil-pbc-topological-inverse-image-stalk (2026-10-09 16:16 UTC, branch head 7efbcee8)

no report file coord/reports/C/lem-weil-pbc-topological-inverse-image-stalk.md in the delivery commit; add the report (with a '## Review by C' section) in the same single commit and re-push.
