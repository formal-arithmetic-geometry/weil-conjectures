1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-proper-flat-finite-dense-open.json` — statement, split; no Mathlib match for the full theorem.
- `dag/nodes/sec-trace-formula/lem-trf-flat-fp-relative-dimension-dense-open.json` — statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-locally-quasi-finite-relative-dimension-zero.json` — statement-only supporting node; no Mathlib match.
- `citations.json` — verbatim statement quotes for every proof citation.

2. Attachments: none. No declaration in `WeilConjectures/` carries the blueprint tag `(blueprint: lem-trf-proper-flat-finite-dense-open)` or states this theorem without `sorry`.

3. WANTED: none.

4. The imported item is the Stacks Project Tag 0B48 theorem, and its hypotheses and conclusion are unchanged. The imported proof was empty, so I supplied the three-step route from Tag 0B48: finite over the dense open gives relative dimension zero there; Tag 081L propagates the bound across the flat locally finitely presented map; Tag 0397 converts relative dimension zero to local quasi-finiteness, and the existing Mathlib leaf `pqf-lem-proper-lqf-finite` concludes finiteness. The two new nodes are genuine intermediate statements rather than clauses of the final finiteness conclusion. The Tag 0397 node is not a duplicate of `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension`: that existing node is an affine ring-map criterion at a prime, whereas this node is the scheme-morphism equivalence needed by the item.

5. I could not finish nothing; the split is complete. No Lean was written or compiled.

## Review by Q74

I read the item source at `literature/stacks-project/flat.tex`, especially the full proof of Tag 0B48 and its cited Tag 081L and Morphisms Tag 0397. Step 1 uses the exact statements of `pqf-lem-finite-qf`, `pqf-lem-qf-locqf-qc`, and the new scheme-level Tag 0397 node; these give quasi-finiteness, local quasi-finiteness, and relative fibre dimension zero for the assumed finite map over `U`. Step 2 uses the new Tag 081L node with `e=0`; its flatness, local finite-presentation, dense-open, fibre-product, and point-dimension hypotheses match the item one by one. Step 3 uses the definitions of local finite presentation and local finite type to justify the finite-type hypothesis required by Tag 0397, then uses Tag 0397 and the existing proper-locally-quasi-finite Mathlib leaf. I checked that every citation quote in `citations.json` is copied verbatim from its node statement, that both new nodes have fresh Mathlib searches (LeanFinder, LeanSearch, Loogle, and Mathlib grep), and that the only Stacks-tag overlap is the explicitly distinguished affine ring-map node above. I also checked the empty-open edge case (excluded by density unless the base has no nonempty opens), finite identity maps, and the failure when flatness is removed; these agree with the stated hypotheses.

## Not duplicates

lem-trf-locally-quasi-finite-relative-dimension-zero vs lem-weil-pbc-ring-quasifinite-zero-fibre-dimension: the new node is the scheme-morphism equivalence between local quasi-finiteness and zero fibre dimension, while the existing node is an affine finite-type ring-map criterion at one prime using the tensor fibre ring.
