# Worker report: `lem-sc-c8`

## Files written

- `dag/nodes/sec-proper-base-change/lem-sc-c8.json`: statement node split and marked `split`; no new nodes were required.

## Attachments

None.

## WANTED

None. The proof follows the imported blueprint proof; the cited source document is present as the node's source record.

## Review findings

The statement is unchanged. The proof's compactification dichotomy is supported by `lem-sc-compactification` and `lem-sc-affine-open-proper`; the proper equal-open case is the identity, and both affine cases use `lem-sc-c2` for degree-two vanishing. The map to the zero group is surjective by the elementary definition of surjectivity. The item now records a source for its proof step and all three required Mathlib searches, which found no matching etale-cohomology theorem.

## Review by C

Reviewed the statement and proof against `stages/1-dag.md` and the unit route `sk-thm-p1`. All cited nodes exist and the proof dependencies are exactly the uses of the sole proof step. `lem-sc-c2` supplies the route's affine vanishing; the compactification and proper-open-affineness facts are recorded as generic tool uses. No Mathlib leaf or new DAG node is omitted. `tools/check_dag.py` passes on the delivery tree.

## What remains

Nothing for stage 1.
