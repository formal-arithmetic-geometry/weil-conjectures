# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-adjunction-two-block-splicing.json`: repaired item statement with five run-collapse and interleaving proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-adjunction-block-run-collapse.json`: new statement-only run-parity and interval-collapse lemma; no Mathlib match.
- `citations.json`: verbatim quotations from the run-collapse node for all five item steps.
- `searches.jsonl`: the prescribed Mathlib search log, including the four searches run for the new run-collapse node.

New nodes: 1 statement-only node. New Mathlib leaves: 0.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, two-block/splicing terms, alternating-string terms, and the recorded blueprint names. No sorry-free project declaration states this item.

## WANTED

- `https://emilyriehl.github.io/files/adjunctions.pdf`, Proposition 3.2.2 and proof, pp. 824--825, and Definitions 3.1.2 and 3.1.8. I read the online paper; an archival copy is not present in `literature/`.
- The paper's cited full combinatorial details in reference [25], §4.2, are unavailable locally. The repaired proof supplies the finite run-collapse/interleaving argument directly after citing the new run-collapse statement.

## Source error

The returned seven-step proof was not valid. Its nested boundary-pairing construction assumes cancellations cross runs and identifies an overlap value that is not present in the integer coordinates. For example, with `m=n=1`, `p=-`, `q=+`, the words `a=(0,2,1,2)` and `b=(0,2,0,2)` have the preimage `c=(0,3,1,3)`; the proposed crossing identification does not describe this word. The old run-join node also had a redundant extremality hypothesis and was only a one-line parity check. The old stack node duplicated the reduction-independence clause already present in the squiggle normal-form statement and the existing common-reduct Mathlib leaf. Both auxiliary nodes were therefore removed.

## Not duplicates

The new `lem-coef-adjunction-block-run-collapse` is strictly smaller than the item: it states only the odd-run parity and the two interval-collapse formulas, and does not state compatibility, existence of a splice, or uniqueness. The removed `lem-coef-adjunction-stack-reduction-pairing` duplicated reduction-order independence already stated by `lem-coef-adjunction-squiggle-normal-form` and abstract common-reduct material in `lem-coef-rewrite-common-reduct`. The removed `lem-coef-adjunction-run-join-alternation` was an elementary join check, not a separate lemma.

## Review by NV

I reread the complete item statement, the cited `def-cbc-enhanced-diagrams-cones` statement, the nearest blueprint ancestor `prop-coef-integral-exceptional-adjoint`, and the Riehl--Verity Proposition 3.2.2 proof and Definitions 3.1.2 and 3.1.8 at the cited online pages. The statement and hypotheses are unchanged: `m,n\ge1`, all four endpoint pairs, singleton strings, the deterministic leftmost reduction, and the exact compatibility condition remain present.

Step 1 cites the new `lem-coef-adjunction-block-run-collapse` statement, which is self-contained and records the odd-run parity, both collapse formulas, no-cross-run cancellation, and preservation of alternating directions. Its statement depends only on the standard-simplex coordinate convention, and the item citation is quoted verbatim in `citations.json`.

Step 2 cites the same run-collapse statement and identifies the compatibility word correctly as `R(v_*R(L_*c)) = d(c) = R(t_*R(U_*c))`, where `d(c)` is the alternating sequence of block-run labels. I corrected an intermediate draft that incorrectly omitted the outer reductions. Steps 3--5 cite the run-collapse statement for the two projected words and apply it to a compatible pair: corresponding binary runs are indexed by the common reduced word; 0-runs of `t_*b` and 1-runs of `v_*a` are singletons; the inverse concatenates the full left runs and shifted full right runs. Join inequalities are forced by the block order, and odd run lengths preserve the alternating parity. Applying `L` and `U` gives the two prescribed restrictions, while any other preimage has the same runs and is therefore equal. Singleton and no-interior-letter cases are included explicitly.

I checked the new node is self-contained, has the required LeanFinder, Loogle, grep and LeanSearch records, and is not a restatement of the item. I checked every item step cites the exact run-collapse sentence it uses, no step cites either removed auxiliary statement, `proof_deps` is exactly the run-collapse node used by all five steps, and the blueprint ancestry and split report remain attached to the imported item. I reran the retained exhaustive checker for `(m,n)=(1,1),(1,2),(2,1),(2,2)`, all four endpoint pairs and strings through the recorded bound; it reports `True` in every case. No Lean source, compiler, Lake, or build tool was run.

## What could not be finished

No part of the repaired split remains unfinished. The only unavailable material is the archival copy of the cited external paper, recorded above as WANTED.
