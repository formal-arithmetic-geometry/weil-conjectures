# Stage 1 report: pqf-lem-qs-intersection-qc

## Files written

- `dag/nodes/sec-nagata-compactification/pqf-lem-qs-intersection-qc.json`: split item.
- `dag/nodes/sec-nagata-compactification/lem-pqf-finite-affine-cover-qc-open.json`: Mathlib leaf, exact declaration `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens` (QuasiCompact.lean:85-89).
- `dag/nodes/sec-nagata-compactification/lem-pqf-affine-intersection-compact.json`: Mathlib leaf, one-line specialization of `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens` (QuasiSeparated.lean:56-64).

## Attachments

None. No declaration tagged `pqf-lem-qs-intersection-qc` or stating this result was found under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`.

## WANTED

None.

## Not duplicates

`lem-pqf-finite-affine-cover-qc-open` vs existing nodes: no existing DAG node states finite affine decomposition of a quasi-compact open; searches covered `dag/nodes` by `isCompact_iff_finite_and_eq_biUnion_affineOpens`, affine-cover, and quasi-compact-open keywords.

`lem-pqf-affine-intersection-compact` vs existing nodes: no existing DAG node states compactness of intersections of affine opens in a quasi-separated scheme; searches covered `dag/nodes` by `quasiSeparatedSpace_iff_forall_affineOpens`, affine-intersection, and quasi-separated keywords.

## Review by M1

I read the imported blueprint proof in `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-zmt/pqf-lem-qs-intersection-qc.md` and the existing conventions node `def-weil-pbc-scheme-conventions`. The item statement uses exactly its notions of quasi-separated scheme and quasi-compact open subscheme. I also read Mathlib `QuasiCompact.lean` lines 78-89 and `QuasiSeparated.lean` lines 56-64. The first new node is exactly the compact-open finite affine union theorem. The second is exactly the forward implication of the affine-open characterization of a quasi-separated underlying space.

Step 1 cites the finite-affine-cover statement, which supplies finite affine covers for both U and V. Step 2 cites the affine-intersection statement for every pair U_i,V_j; distributing intersection over the finite unions gives a finite union. The remaining finite-union compactness and openness assertions are elementary topological facts from the definitions and the cited compactness statements. I checked empty and singleton finite covers, and the affine case, where the result reduces directly to the second Mathlib leaf.

The original imported step incorrectly cited only the conventions bundle while using the affine basis theorem and affine-intersection theorem. I replaced that paragraph with two explicit steps and added the exact Mathlib searches, blueprint references, and verbatim citations.

## Second reading by M1

- Item statement: checked against the imported blueprint node and the scheme, quasi-separated, quasi-compact, and open-subscheme definitions; the hypotheses and conclusion agree, including the empty and affine cases.
- New node `lem-pqf-finite-affine-cover-qc-open`: checked against `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens` in `QuasiCompact.lean` lines 85-89; exact Mathlib leaf, self-contained after its definition dependencies, and true for the empty and singleton covers.
- New node `lem-pqf-affine-intersection-compact`: checked against the forward implication of `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens` in `QuasiSeparated.lean` lines 56-64; exact one-line specialization, including the affine case and empty intersection.
- Step 1: checked that the cited finite-affine-cover statement supplies finite affine unions for both quasi-compact opens; no unstated hypothesis is used.
- Step 2: checked distributivity over the finite unions, the cited pairwise affine-intersection compactness, finite-union compactness, and openness of intersections; the finite-union and openness portions are elementary.
- Delivery checks: `deliver.py M1 pqf-lem-qs-intersection-qc --no-push` passed preflight before and after repair.

Changes made:

- Added `def-weil-pbc-quasi-compact-scheme` to the statement dependencies of the item and both new leaves, because that node defines quasi-compactness while the conventions node only collects terminology.
- Kept both Mathlib leaves and the two-step proof: neither new node duplicates an existing DAG node, and the item is not restated as a node.
