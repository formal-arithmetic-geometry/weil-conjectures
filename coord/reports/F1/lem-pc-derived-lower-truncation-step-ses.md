Files written:

- `lem-pc-derived-lower-truncation-step-ses.json` — statement, split proof, no new nodes.
- `citations.json` — verbatim statement excerpts for every proof citation.

Attachments: none.

WANTED: none.

What was checked and changed: the item was unsplit and had the correct chain-level statement. No exact sorry-free declaration with the blueprint tag exists in either Lean source checkout. The existing child `lem-pc-derived-lower-truncation-step-triangle` uses this item and confirms that its quotient complex must be the two-term complex `C_m(K)`, rather than the shifted cohomology object itself. I retained the statement and filled its proof, proof dependencies, document origin, split report, and blueprint realization. The Mathlib search found only generic `CochainComplex.shortComplexTruncLE_shortExact` and related truncation morphisms; no declaration states the explicit two-term quotient together with its quasi-isomorphism to `H^m(K)[-m]`, so this is not a Mathlib leaf. No new node was needed because each argument is a direct degreewise calculation from the definitions.

## Review by F1

I read the item and its child triangle node, the Stacks homology source for Tag 0118, and the existing definition nodes `def-sp-abelian` and `def-weil-abstract-derived-category`. Step 1 uses only the abelian-category kernel/image operations and the complex definition: I checked degree `m`, degree `m+1`, and all higher degrees separately, and checked that the induced differential squares to zero. Step 2 uses the stated cohomology and quasi-isomorphism definitions: the map is the inclusion of cycles modulo boundaries, `C_m(K)` has cohomology `H^m(K)` in degree `m`, zero in degree `m+1`, and zero elsewhere. Step 3 uses the functoriality of cohomology and the fact that a chain map preserves kernels and images; I checked the induced maps on both truncations and on the quotient complex commute with the canonical inclusion. The citations quote the exact clauses used from the cited nodes. I tested the construction on the zero complex and on a complex concentrated in degree `m` (where the sequence reduces to `0 -> K^m -> K^m -> 0` and the quasi-isomorphism is an identity), and on a complex with one nonzero differential (where the degree-`m+1` kernel is exactly its image). No statement correction was required.

## Second reading by F1

- Item statement: checked against Stacks Tag 0118 (Section `homology-section-truncations`) and Tag 08J5 (Remark `derived-remark-truncation-distinguished-triangle`); the hypotheses and conclusions agree.
- Step 1: checked degree-by-degree against Tag 0118 and the cited definitions; the kernel at degree `m+1` is exactly `im(d^m)`, and the differential condition follows from `d^{m+1} d^m = 0`.
- Step 2: checked against Tag 0118 and the cited quasi-isomorphism definition; the only nonzero cohomology of `C_m(K)` is `H^m(K)`, so the map is a quasi-isomorphism.
- Step 3: checked against functoriality in `def-weil-abstract-derived-category`; a chain map induces all displayed maps and the canonical inclusion commutes.
- New nodes: none; existing-node searches and Mathlib searches are recorded in `searches.jsonl`.
- Small cases: checked the zero complex, a complex concentrated in degree `m`, and a complex with one nonzero differential.
- Changed `created.item` to this item because it incorrectly named the child triangle item, and added this required second-reading section.
