# Stage 1 delivery: `lem-weil-pbc-constant-sheaf-sections-connected`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-sheaf-sections-connected.json` — statement; split into three proof steps; Mathlib verdict: no exact match for the etale-scheme computation.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-sheaf-sections-locally-constant.json` — statement-only reusable Stacks 03P5 identification; Mathlib verdict: no exact match, unsplit.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-connected-locally-constant-map.json` — statement; Mathlib leaf matching `IsLocallyConstant.apply_eq_of_preconnectedSpace` at pinned `Mathlib/Topology/LocallyConstant/Basic.lean:147-149`; fibre formulation checked against `iff_isOpen_fiber` at lines 101-102.

## Attachments

None. The assigned item has `lean_audit` state `none` on both branches and no Lean declaration to attach.

## WANTED:

WANTED: none. The proof follows the Stacks document named in the nodes; no missing document was needed.

## What was wrong in the node, blueprint, or brief

The imported item had an empty proof despite its source explicitly reducing sections of the constant sheaf to Zariski locally constant maps and then to constant maps on a connected space. The reusable first reduction is now deliberately statement-only, with the exact source labels: Remark 59.23.2 (Tag 03P5) and Lemma 59.15.8 (Tag 03O3); its cited representability input is Example 39.5.6 (Tag 03YW). The connectedness argument is represented by a Mathlib leaf, with the pinned source line and the fibre-open equivalence recorded.

The global `check_dag.py` run reports six pre-existing reachability warnings for unrelated nodes (`lem-weil-pbc-constructible-finite-pushforward-approximation`, `lem-weil-pbc-constructible-finite-pushforward-noetherian`, `lemma-weil-pbc-constructible-approximation`, `lemma-weil-pbc-finite-cover-killing`, `lemma-weil-pbc-finite-stage-killing`, and `lemma-weil-pbc-pushout-monicity`); it reports zero cycles and no issue involving this delivery. `review_split.py lem-weil-pbc-constant-sheaf-sections-connected` passes and recognizes both new nodes.

## What could not be finished, and why

The reusable Stacks identification node is intentionally statement-only and `unsplit`, and must be handled as a subsequent Stage 1 item. No Lean files were written or compiled, as required for Stage 1.

## Review by C1

I independently checked that the statement is exactly the connected-scheme specialization of Stacks Remark 59.23.2 (Tag 03P5), that the reusable node is statement-only, that the representability citation is Lemma 59.15.8 (Tag 03O3), and that the Mathlib leaf records Basic.lean:101-102 and :147-149. The item is ready for lead review; the only follow-up is splitting the new reusable Stacks node.
