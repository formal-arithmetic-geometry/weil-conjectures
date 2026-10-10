# Stage 1 report

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-qc-open-eq-eventually.json`: item split, no new nodes.
- `citations.json`: one verbatim citation for the proof step.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` states this item exactly. The Mathlib declaration `AlgebraicGeometry.exists_map_preimage_eq_map_preimage` was considered but does not identify the explicit stage selected by the project's definition.

## WANTED

None.

## Not duplicates

None: no new node was created.

## Review by C1

I read the imported item and the complete statement of `def-nagata-qc-open-equality-stage`. That definition supplies the finite affine charts, finite basic-open presentations, both radical-containment power identities, and the finite upper-bound stage. The sole proof step uses exactly its final parenthetical assertion: after transport to any later index, the first identity gives each $D(f_{1jk,\\lambda})$ inside the finite union of the $D(f_{2\\ell k,\\lambda})$, and the second identity gives the reverse inclusion. I checked the pointwise algebra: at a point where $f_{1jk,\\lambda}$ is nonzero, its power identity prevents all $f_{2\\ell k,\\lambda}$ from vanishing; the converse is symmetric. Finite unions on each affine chart and the affine cover then give both global inclusions. I also searched the Lean source for the item tag and its concepts; no project declaration exists. The required Mathlib searches found `exists_map_preimage_eq_map_preimage` as a related existence theorem, while Loogle rejected the pattern, grep found no matching project-specific declaration, and LeanSearch was unavailable; these results are recorded in the item node.

## What was wrong or incomplete

The imported statement was shorthand and did not identify the descended opens or the selected witness stage. I expanded it to refer to the data constructed by the definition and changed status from `imported` to `split`. The imported proof had no citation and a null elementary flag; it now cites the definition node and marks the direct chartwise argument elementary.

## Unfinished

Nothing.

## Second reading by C1

- Item statement: checked against the imported blueprint item and `def-nagata-qc-open-equality-stage`; the selected stage, transported basic opens, and quantifier λ ≥ λ_{W_1=W_2} are explicit; verdict: agrees.
- Step 1: checked against the full statement of `def-nagata-qc-open-equality-stage` and its final parenthetical clause; the two radical-containment identities give the two chartwise inclusions, and finite unions and the affine cover give the global inclusions; verdict: elementary and complete.
- New nodes: none; no B1–B7 audit or duplicate search was needed beyond confirming that the cited definition is the existing node.
- Edge cases: empty basic-open families and empty opens give both inclusions vacuously; on a single affine chart the argument is the usual radical-containment test; exponent 0 or 1 does not invalidate the pointwise implication.
- Changes: none; the split statement, proof, citation quote, and recorded Mathlib searches were already consistent and the dry-run preflight passed.
