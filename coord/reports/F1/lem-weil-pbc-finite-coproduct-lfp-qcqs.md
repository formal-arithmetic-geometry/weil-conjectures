# lem-weil-pbc-finite-coproduct-lfp-qcqs

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-coproduct-lfp-qcqs.json`: split into three steps, proving quasi-compactness, quasi-separatedness, and local finite presentation, including the empty family.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-quasi-separated-affine-cover-criterion.json`: new Mathlib leaf, the two directions of the affine-cover criterion; Mathlib `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens` (Morphisms/QuasiSeparated.lean:56) and `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover` (same file:181), with the absolute scheme identification at :133. Searched the whole blueprint by phrase and Tag 01KO, the DAG by phrase and declaration, and the read-only slopmaster2 Lean source by notion and blueprint id; no duplicate found.
- `coord/reports/F1/lem-weil-pbc-finite-coproduct-lfp-qcqs.md`: this report.

## Attachments

None. The item has `lean_audit.slopmaster2.state = none`; no declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` or `Comparator/` states it or the new criterion exactly.

## WANTED

None. Read the obtained Stacks source in `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/`: Schemes Lemma Tag 01KO, label `lemma-characterize-quasi-separated`, `schemes.tex:4125`; Morphisms Lemma Tag 01TQ, label `lemma-locally-finite-presentation-characterize`, `morphisms.tex:4096`. The generated Stacks checkout is absent in this worktree but present at the cited local clone.

## Corrections and limits

The imported new item had an empty proof. Its existing statement and the blueprint reference agree with the source. The chosen proof uses the coproduct leaf's actual public statement, so it does not rely on the internal construction of that leaf. Its use of the criterion is limited to compact intersections of affine opens, including the empty case. No Lean code was written or built.

`python3 tools/review_split.py lem-weil-pbc-finite-coproduct-lfp-qcqs` passes. `python3 tools/check_dag.py` reports seven unreached nodes and eleven off-route uses of `thm-constructible-serre` elsewhere, and reports no error on this item or its new leaf.

## Review by F1

I read Stacks `schemes.tex`, `lemma-characterize-quasi-separated` (01KO, lines 4125-4155), and `morphisms.tex`, `lemma-locally-finite-presentation-characterize` (01TQ), and compared their hypotheses with the item's three clauses. I checked the public `lem-weil-pbc-scheme-coproduct-family` statement: the summands are open and closed, disjoint, and cover the coproduct, with the claimed mapping property. Step 1 then proves quasi-compactness by a finite union of quasi-compact summands, explicitly including the empty union. In step 2 the affine opens from each summand cover V; cross-summand intersections are empty and same-summand intersections are quasi-compact by clause (1) of the new criterion. Clause (2) gives quasi-separatedness exactly as in 01KO, including the empty affine cover of the empty scheme. In step 3, `def-sbc-locally-finite-presentation` says finite presentation at each point is witnessed by affine source/target neighbourhoods and a finitely presented ring map; the open summand identification transfers those witnesses to g. No global finite-presentation hypothesis was silently used.

The new criterion is self-contained and strictly narrower than the item. I checked pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`: `quasiSeparatedSpace_iff_forall_affineOpens` starts at `Morphisms/QuasiSeparated.lean:56`, the absolute-scheme identification is at 133, and `Scheme.quasiSeparatedSpace_of_isOpenCover` starts at 181. Together they supply the two stated clauses without an additional theorem. Its source, definition citations, blueprint provenance, Mathlib searches, and absence of proof steps satisfy B1-B8; the worker added the numeric Mathlib line after my B6 review. The item and leaf are absent from the read-only slopmaster2 source as reported, and the DAG/blueprint searches found no exact duplicate. The three steps form a real proof with no new node restating the item and no off-route tool or cycle. I checked the one-summand and empty-family cases and the locality hypothesis in each step under E1-E6. `review_split.py` passes; the global reach/route findings concern other items.

