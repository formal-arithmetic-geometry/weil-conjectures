1. Files written:

- `dag/nodes/sec-zeta-weil/lem-weil-alternating-form-dimension.json` — split item; no direct Mathlib parity theorem.
- `dag/nodes/sec-zeta-weil/lem-weil-bilin-form-nondegenerate-det.json` — Mathlib leaf, exact match to `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` at `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:550`.
- `citations.json` — citation for the item proof step.

2. Attachments: none. No declaration tagged `(blueprint: lem-weil-alternating-form-dimension)` or stating this item exactly was found under `WeilConjectures/` in the reference source.

3. WANTED: none.

4. No statement correction was needed. The imported proof paragraph was mathematically sound but left the basis choice, determinant identities, and the use of `char(K) ≠ 2` implicit; these are explicit in the split. The only non-elementary implication is isolated as the Mathlib leaf, and its statement was checked against the theorem source. Searches found no duplicate DAG or blueprint node for this determinant criterion or for the parity conclusion.

5. Nothing remains unfinished.

## Not duplicates

`lem-weil-bilin-form-nondegenerate-det` vs `lem-sbc-trace-discriminant-evaluation-etale-fibre`: the existing node concerns an evaluated trace discriminant and etaleness of a scheme-theoretic fibre, while the new node is the general bilinear-form Gram determinant criterion.

## Review by Q123

I read the item in `dag/nodes/sec-zeta-weil/lem-weil-alternating-form-dimension.json`, the current blueprint statement and proof in `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-prop-reciprocity/lem-weil-alternating-form-dimension{,.proof}.md`, and the Mathlib source at `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:550-552`. The sole item step chooses a finite basis, forms the Gram matrix, uses alternation for `Bᵀ = -B`, uses determinant transpose and negation identities, and invokes the cited node exactly for nonzero determinant. The final cancellation and odd/even contradiction use only field arithmetic and the hypothesis `char(K) ≠ 2`. I verified that the cited node states precisely the needed determinant nonvanishing, and that its Mathlib declaration is an exact match. I also checked the whole DAG and blueprint for duplicates and recorded all required Mathlib searches with their returned hits.
