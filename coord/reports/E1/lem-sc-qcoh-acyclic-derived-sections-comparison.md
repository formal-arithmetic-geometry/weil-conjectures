Files written:

- `lem-sc-qcoh-acyclic-derived-sections-comparison.json` (statement, split; no new nodes; Mathlib searches found no matching derived comparison).
- `citations.json` (verbatim statement excerpts for every cited node and step).

Attachments: none.

WANTED: none.

The imported item had no proof. I checked the source route against Stacks Tags 08D4, 08D5 and 0AVW. The split uses the existing DAG statements for qcqs higher-direct-image quasi-coherence, affine vanishing, Leray degeneration, the unbounded cohomological bound, and the truncation spectral sequence. No helper node was created because a new generic comparison node would restate the item.

## Review by E1

I read the item source passage in `literature/stacks-project/perfect.tex` and checked its hypotheses against the node: `f` is qcqs, the vanishing is for every quasi-coherent module in positive degrees, `V` is affine, and `E` is in `D_QCoh`. Step 1 uses the statement of `lem-pc-finite-support-hi` for quasi-coherence of higher direct images, `lem-pc-affine-vanishing` for affine higher-cohomology vanishing, and `lem-pc-leray-degenerate-sections` for the edge comparison; these statements say exactly the properties used. The restriction to `f^{-1}(V)` and the product-preservation check are direct consequences of the definitions and the product universal property.

Step 2 uses `lem-pc-unbounded-derived-functor-cohomological-bound` exactly in its upper-bound form with `N=1`, and the `D_QCoh` meaning from `def-pc-derived-category`; the truncation triangle then removes the negative tail. Step 3 uses `thm-sp-truncation-e2`, whose statement gives the `E_2^{p,q}=R^p v(H^q(K))` page and finite abutment filtration. Since Step 1 gives vanishing for `p>0`, only the `p=0` graded piece remains, yielding the section comparison. Step 4 uses the definition of `Rf_*` and the universal property in `def-weil-pbc-sheafification`; both cited statements explicitly provide the sheaf/cohomology and unique factorization clauses used. Naturality and restriction compatibility are inherited from the functorial constructions in the cited spectral sequence and derived functor statements.

I tested the edge cases `E=0`, `i=0`, and `E=F[0]` for a quasi-coherent `F`: the comparison reduces respectively to zero, the ordinary acyclic section comparison, and `H^0(U,F)=\\Gamma(U,F)`. The four Mathlib searches were run on 2026-10-11 (LeanSearch was unavailable); no Mathlib declaration states this scheme-level unbounded comparison.

## Second reading by E1

- Item statement: checked against Stacks Tags 08D4, 08D5, and 0AVW; qcqs, affine-open, quasi-coherent-acyclic, all-integer, naturality, restriction, and sheafification clauses are present; verdict: consistent.
- Step 1: checked [lem-pc-finite-support-hi], [lem-pc-affine-vanishing], [lem-pc-leray-degenerate-sections], and [def-pc-derived-direct-image]; restriction to the affine inverse image and product preservation are the stated qcqs/section facts; verdict: accepted.
- Step 2: checked [lem-pc-unbounded-derived-functor-cohomological-bound] with `N=1` and [def-pc-derived-category]; the truncation triangle removes the negative tail in degree zero; verdict: accepted.
- Step 3: checked [thm-sp-truncation-e2] and [def-pc-derived-category]; bounded-below truncation gives the stated E2 page, and vanishing of positive rows leaves the p=0 graded piece; verdict: accepted.
- Step 4: checked [def-pc-derived-direct-image] and [def-weil-pbc-sheafification]; affine restriction comparisons identify the presheaf with the restriction of `f_*H^i(E)`, and the sheafification universal property gives the final identification; verdict: accepted.
- New nodes: none; the split has no statement-only helper nodes to audit, and all cited generic ingredients pre-exist in the DAG. Existing-node searches were checked by tag and key phrase.
- Small cases checked: `E=0`, `i=0`, `E=F[0]`, the zero scheme, and a field-valued affine base; no statement changes were needed.
- Changes: added this second-reading record only; no mathematical or node-content changes were required.
