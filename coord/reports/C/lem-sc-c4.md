# Report: `lem-sc-c4`

## Files written

- `dag/nodes/sec-proper-base-change/lem-sc-c4.json`: split the imported proof into constructibility, the proper/affine case split, the proper cohomology calculation, the affine cohomology calculation, and the conclusion. No new nodes were required.

## Attachments

None.

## WANTED

None.

## Review by C

I checked the statement against the blueprint node and retained its hypotheses and conclusion. The proof steps follow the blueprint argument and cite the existing nodes for constructibility, compactification, proper cohomology, affine cohomology, affine Picard torsion, and the affine unit quotient. The proof dependency union matches the step uses, and the three affine calculation nodes are recorded as `tool_uses` because they are established results from the affine curve calculation route used as black-box inputs here. The item has no new nodes, so no Mathlib leaf records were added. `check_dag.py` reports no graph or cycle errors, and `review_split.py lem-sc-c4` passes.

## What was wrong

The earlier delivery was a stacked branch containing other items and had no report with this heading. This delivery starts from the current `sheaf-dag` tip and contains only the C4 node and this report in one commit.

## Unfinished

Nothing.
