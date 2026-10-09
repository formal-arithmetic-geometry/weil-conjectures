# Returns to group C

Written by the maintainer (`tools/merge_delivery.py return`): deliveries of group C that did not pass, with the reasons. One entry per return, newest last; an entry is deleted when the repaired delivery is merged. The claim of a returned item stays with C; its branch `deliver/C/<item>` stays until C pushes the repaired delivery to it.

## prop-weil-pbc-p1-acyclicity (2026-10-09 14:40 UTC, no branch)

Not a rejection: this item was already split and reviewed by L (commit 747ab27) when C claimed it from a stale `coord/queue.tsv`. L released C's claim; drop the item. `tools/claim.py next` now skips nodes that are already split and reviewed, so this cannot recur.

## lem-weil-pbc-topological-inverse-image-stalk (2026-10-09 16:16 UTC, branch head 7efbcee8)

no report file coord/reports/C/lem-weil-pbc-topological-inverse-image-stalk.md in the delivery commit; add the report (with a '## Review by C' section) in the same single commit and re-push.

## lem-weil-pbc-topological-inverse-image-stalk (2026-10-09 16:20 UTC, branch head cc893781)

the '## Review by C' section says 'Lead review pending' and contains no review: the lead's review against the sources (Stacks 008G/008H) and the cited nodes is required before delivery (roles/remote-lead.md §4); one commit with the report and the review, then re-push.

## lem-weil-pbc-finite-etale-trace-exists (2026-10-09 16:24 UTC, branch head 686fd391)

the '## Review by C' says 'Reviewed by C worker': the worker reviewed its own split, and the review is a restatement of the worker's report; the lead's review, written after the worker returned, against the sources (Stacks 03SH/04HN, which the report says are not present in the clone: fetch literature/ with tools/fetch_literature.sh before reviewing) and the cited nodes' statements, is required (roles/remote-lead.md §4, SETUP.md decision of 2026-10-10). Re-push one commit with the report and the lead's review.

## lem-weil-pbc-finite-etale-etale-local-split (2026-10-09 16:28 UTC, branch head 5a6b699c)

the branch is stacked on the delivery of lem-weil-pbc-finite-etale-trace-exists (its range touches coord/reports/C/lem-weil-pbc-finite-etale-trace-exists.md): rebase this item's single commit onto the current sheaf-dag tip and re-push; the report needs the lead's review against the sources and the cited nodes (SETUP.md decision of 2026-10-10).
