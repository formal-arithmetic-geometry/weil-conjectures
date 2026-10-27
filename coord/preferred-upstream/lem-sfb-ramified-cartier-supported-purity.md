# Maintenance route decision, 2026-10-24

Maintenance route decision, 2026-10-24, for the repeated NU failure. Q159 correctly identified an unresolved route/data conflict: the unchanged item requires codimension-one absolute purity for arbitrary Noetherian regular pairs, whereas the approved smooth-purity theorem cannot supply it. Re-admit the existing finite-coefficient statements lem-per-gabber-regular-pair-purity and lem-per-regular-immersion-class-calculus as unsplit inputs for this item. Their old proof graphs and reviews are withdrawn from active records and their stage-1 work is released separately; no old adic, alteration or duality split is restored by this decision. This discharges Q159's missing route-decision objection for these two citations; it does not certify the item or either input. Preserve the item's statement, source, statement dependencies, ordinary etale site and actual unit/Kummer normalization. Reuse the saved seven-step candidate and logged searches, checking all current statements and citations. Keep the live lem-pur-cartier-pair-tensor-addition for this item's additivity. Maintenance Q26 has separately re-admitted lem-per-noetherian-supported-product-calculus and three other finite-coefficient construction interfaces as unsplit inputs for class calculus (see coord/changes/20261024-Q26-class-calculus-inputs.md); this does not restore their old proofs. Run one no-push delivery to completion, repair its diagnostics, then deliver under the normal independent review. Do not repeat the old BLOCKED disposition on the ground that these two inputs are dropped. Every other route restriction, including no SGA except the specified SGA 5 pairing, remains in force. Details: coord/changes/20261024-NU-supported-cartier-purity-route.md.

Read the current coord/repair-notes/lem-sfb-ramified-cartier-supported-purity.json and the change record before applying historical BLOCKED notes or the old sandbox report. Those reports describe the state before this maintenance commit. The theorem inputs are still work to prove; citing an unsplit dependency is normal stage 1.

## Stage-1 routing correction, 2026-10-24

The repair is stage 1. The earlier keep_plan=true flag was invalid: the live
item is unsplit with empty proof/proof_deps and has no reviewed plan or Lean
record to retain. It enabled the queue's intentional keep-plan exception and
created a second stage-2 row; claim.py chose the highest stage and
delivery_stages.py chose the last row. The flag is now false and the duplicate
stage-2 row has been removed. See
coord/changes/20261024-NU-supported-cartier-stage1-routing.md.

Resume the saved stage-1 candidate in
/home/ubuntu/weil-newtargets-sandbox/NU/lem-sfb-ramified-cartier-supported-purity/
(node, report.md, citations.json and searches.jsonl). Validate it against the
current live records with batch2/deliver.py NU
lem-sfb-ramified-cartier-supported-purity --no-push, then follow the stage-1
worker brief and independent review path. The stage-2 sandbox contains only
brief markers; its "found 0" diagnostic was a consequence of the wrong lane.
The historical H1/H2 return on e5f07abe70bb describes that routing failure;
it does not require writing Lean before the stage-1 split is reviewed.
The finite-coefficient route decision above and all content checks still apply.
