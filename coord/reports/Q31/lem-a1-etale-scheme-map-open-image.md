# Worker report

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-etale-scheme-map-open-image.json`: completed the one-step split; no new nodes or Mathlib leaves.
- `citations.json`: one verbatim quotation for the existing dependency used by the proof.
- `report.md`: this stage-1 report.

## Attachments

None. I searched the read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` tree for the exact item id, the Tag 06NF/`etale-image-open` wording, and the open-image algebraic-space terminology. No sorry-free project declaration states this complete theorem. The existing node `lem-a1-space-etale-open-image` is the required DAG dependency, not a Lean attachment: it states a more general theorem for representable etale maps of algebraic spaces.

## WANTED

None. The Stacks source and the existing general DAG node are present locally.

## What was wrong or changed

The imported item was `status: unsplit` with no proof. The DAG already contains `lem-a1-space-etale-open-image`, which strictly generalizes the item: its source and target are arbitrary algebraic spaces, while this item specializes the source to the scheme algebraic space `h_U`. I therefore added one proof step applying that node with `E=h_U`, `F=X`, and `q=f`; this supplies the open image, representable open immersion, exact point-image equality, and representable surjective etale factorization. Creating helper nodes for these clauses would duplicate that existing statement, so none were created. No statement, hypothesis, or conclusion was changed.

The item is not a Mathlib leaf. Its inherited Mathlib searches remain recorded unchanged because the statement and search question did not change.

## Review by Q31

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, delivery-errors B–E, the `sec-purity-real-sheaves` chapter and `sk-p-real-rankin` unit, the complete item node, and the complete statement of `lem-a1-space-etale-open-image`. I also read Stacks `spaces-properties.tex`, Tag 06NF (`lemma-etale-image-open`, lines 536–559), including its preceding factor-through-open-subspace and characterize-surjective lemmas.

The single proof step uses only the cited general node. That statement says verbatim that a representable etale map `q:E→F` has an open point image corresponding to an open subspace `I⊂F`, factors through `I`, and becomes representable surjective etale onto `I`. Substituting the scheme algebraic space `h_U` for `E`, `X` for `F`, and `f` for `q` gives every item clause. The point-image sentence specializes from `|h_U|` to the stated `|U|`; identifying `h_U` with the scheme `U` is the definition-level specialization already present in the item. The open-subspace conclusion gives the representable inclusion `j`, and the factorization gives `f_f` with the required properties. No hidden proof of the cited node is used.

I checked edge cases of the specialization: `U=∅` gives the empty open image and the unique map to it; `f` an open immersion gives its usual open image; and a surjective `f` gives `X_f=X`. The cited node's hypotheses exactly match the item's representability and etaleness assumptions, with no quasi-compactness, separation, or finiteness condition added. The item's field-valued point-class convention matches the convention in the general node. There are no new nodes, duplicate pairs, hollow definitions, statement disputes, or tool uses outside the unit. The proof step is short and contains no hidden lemma. No Lean files were written or compiled.

## Unfinished work

None for this stage-1 split. The general dependency remains unsplit for its own queue item; this delivery only completes the present specialization.
