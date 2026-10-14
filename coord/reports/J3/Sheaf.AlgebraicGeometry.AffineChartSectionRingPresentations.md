## What changed

The target theorem now combines two strictly smaller intermediate statements: the initial
upper-tail projection isomorphism and the remaining chart presentation conjunction. Both
intermediate proofs are left as named stage-3 holes; the target proof itself is complete.

## Proved and sorry left

Proved `affine_chart_section_ring_presentations` by combining the two intermediate results.
Sorry remains in `affine_chart_section_ring_presentations_iso` and
`affine_chart_section_ring_presentations_tail`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The planned geometric proof is substantially larger than the available module context, so it
was decomposed into two independently stated strict subclaims.

## New nodes

`new-affine-chart-section-ring-presentations-iso` and
`new-affine-chart-section-ring-presentations-tail` are added under `dag/nodes/sec-picard-framework`.

## Earlier second reading (a previous round; superseded)

Pending second reading; the target compiles and its signature is unchanged.

## Earlier second reading (a previous round; superseded)

Pending second reading; the target compiles and its signature is unchanged.

## Second reading by J3

1. Compared the delivered target module with the repository version: all existing declaration signatures are byte-for-byte unchanged; only the target proof and its two plain proof imports differ. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the two named split-off theorems, with no forbidden declarations or hollow definitions. Verdict: pass.
3. Checked both split-off statements against their declarations and nodes. They are strict subclaims of the target, mathematically well-typed, and their source/docstring explanations identify the deferred geometric arguments. Verdict: pass.
4. The target proof uses both split-off results and preserves the unit route; imports are needed for the statements or these proof calls, and no pruning is available. Verdict: pass.
5. DAG node metadata matches the theorem names, statements, modules, proof origin, and split status. Verdict: pass.

Changed the split-off theorem docstrings to include complete proof sketches, and added this second-reading record. No signatures or imports were changed.
