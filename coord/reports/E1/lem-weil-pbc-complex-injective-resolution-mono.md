# Stage 1 report: `lem-weil-pbc-complex-injective-resolution-mono`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-complex-injective-resolution-mono.json`: repaired the returned item with one proof step citing the public 05T6 statement.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-subcategory-right-resolution-05T6.json`: added the required unsplit Stage 1 node for Stacks 05T6, part (1).
- `coord/reports/E1/lem-weil-pbc-complex-injective-resolution-mono.md`: this report.

## WANTED

None. The source is available in the project Stacks checkout at `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/derived.tex`.

## Findings and changes

The prior delivery was returned because its three construction steps did not justify the induction, the killing of cohomology, or the quasi-isomorphism calculation. I checked the DAG for existing `05T6` nodes and found none. The repair records Stacks Lemma Tag 05T6 (`lemma-subcategory-right-resolution`, line 5387), part (1), as a dedicated unsplit node with the exact subset hypothesis and conclusion requested by the return.

The item now has one proof step: take the subset to be the injective objects. The zero object is injective, and the enough-injectives hypothesis gives every object as a subobject of an injective. The 05T6 conclusion then matches the item term for term, including the degreewise monomorphisms, quasi-isomorphism, injective terms, and vanishing below `a`. The new node's `created.item` is this item, and its statement is intentionally unsplit because this delivery records the cited source lemma rather than reproving it.

## Verification

- `python3 tools/review_split.py lem-weil-pbc-complex-injective-resolution-mono`: PASS, one new unsplit node.
- `python3 -m json.tool` on both changed node files: PASS.
- `python3 tools/check_dag.py --cycles`: no cycles or self-loops; any unrelated reachability notes are pre-existing.

## Unfinished

Nothing in the claimed item. No Lean files were written or compiled.

## Review by E1

I reviewed the return point by point against Stacks `derived.tex` Tag 05T6 at line 5387. The new node states part (1) with the required abelian category, subset containing zero, subobject condition, lower bound, degreewise injective maps, injective terms, and quasi-isomorphism. The item proof specializes exactly to injective objects and identifies the two hypotheses supplied by enough injectives. The branch contains one item commit, no private module, and the required split report.
