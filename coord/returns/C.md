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

## lem-weil-pbc-filtered-colimit-tensor-varying-rings (2026-10-09 16:38 UTC, branch head af47dd6b)

the '## Review by C' is a mechanical check (statement against the unit, steps name dependencies, searches recorded), not the lead's review against the source (Stacks 00DD) and the cited node def-weil-pbc-category-colimit (SETUP.md decision of 2026-10-10, roles/remote-lead.md §4); also the four new nodes carry proof steps while their status is unsplit: a node is either split (its proof reviewed) or unsplit (no proof); put the arguments in the item's steps or make the new nodes proper split items. Re-push one commit with the lead's review.

## lem-weil-pbc-sheaf-of-modules-from-basis (2026-10-09 16:56 UTC, branch head 68ba8b16)

(1) '## Review by C' says 'Pending lead review': not a review (SETUP.md decision of 2026-10-10: a delivery needs the lead's own review against the sources and the cited nodes). (2) The three new nodes are not self-contained statements: 'Let X and B be as in the basis extension construction', 'the sheaf of modules obtained from compatible module data' refer to a construction that exists in no node; each node must state its hypotheses in full (stages/1-dag.md), and lem-weil-pbc-basis-extension-sections is a construction, not a statement. (3) WANTED claims sheaves.tex is absent: it is at literature/stacks-project/sheaves.tex (labels lemma-extend-off-basis, lemma-extend-off-basis-module, ...); follow the proofs of 009L/009N/009T/009U with exact sources instead of an agent-written sketch. (4) Step 1 argues with a 'finite subcover'; the hypothesis gives a finite refinement, not a subcover. (5) Stacks tags 009L/009N/009T/009U must be cited per step with the lemma labels.

## lem-weil-pbc-proj-standard-open-inclusion (2026-10-09 16:56 UTC, branch head ff126e05)

Branch stacked on deliver/C/lem-weil-pbc-sheaf-of-modules-from-basis (it carries that item's report and nodes); one branch per item on top of sheaf-dag (roles/remote-lead.md). Re-push on the current sheaf-dag after the other delivery is merged or on its own base.

## lem-weil-pbc-zariski-h0-proper-henselian-pair (2026-10-09 17:09 UTC, branch head 9906be5f)

Branch stacked on deliver/C/lem-weil-pbc-proj-standard-open-inclusion (carries that item's report); one branch per item on top of sheaf-dag. Note: lem-weil-pbc-proj-standard-open-inclusion has since been split by L (C released its claim); rebase on the current sheaf-dag and re-push.
