# Stage-1 report: lem-sfb-finite-affine-proetale-refinement

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-affine-proetale-refinement.json`: split into five proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node at every step.
- `report.md`: this review.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, the blueprint tag, and the finite-affine/pro-etale refinement terminology; no exact sorry-free project declaration states this item.

## WANTED

None.

## Issues checked

The imported statement is well-typed and was retained. Its Noetherian and quasi-separated hypotheses are stronger than the local argument needs, but no hypothesis was removed. No new node was created: the route uses the existing pro-etale-site definition, weakly-etale stability statement, quasi-separated affine-intersection Mathlib leaf, finite affine-cover Mathlib leaf, affine-fibre-product Mathlib leaf, and fibre-product definition. The item’s recorded Mathlib searches were rerun with two semantic phrasings, Loogle, grep, and LeanSearch; they found only general affine-cover APIs and no theorem stating the complete pro-etale refinement.

## Not duplicates

None: no new nodes were created.

## Review by Q116

I read the item node, the `sec-six-functors-basics` chapter record, the `sk-prop-scalar-six` unit record, the main-20261015 blueprint section and the full `det-prop-scalar-six-ctf.proof.md`, especially Step (2), which is the source for this item. I also read the complete statements of `sk-def-pe-site`, `sk-lem-pe-weakly-etale-stability`, `def-pc-fibre-product`, `lem-weil-pbc-quasi-separated-affine-cover-criterion`, `lem-weil-pbc-qcqs-finite-affine-open-cover`, and `lem-weil-pbc-fibre-product-affine-spectra`.

Step 1 applies the site definition directly to the affine open $U_\\alpha$ of the target $S$, so it yields exactly the finitely many indices and affine opens appearing in the item. Step 2 checks every map to $S$: the site definition supplies weak étaleness of each $W_i$, the cited stability statement supplies base change, open restriction, and composition, and the fibre-product definition identifies the composite with the displayed map. Step 3 checks the arbitrary affine test open $W$: quasi-separatedness gives quasi-compactness of each $W\\cap U_\\alpha$, and the finite-affine-cover leaf supplies finite affine covers of those intersections; their finite union covers $W$. Step 4 forms the intersections of the selected $V_{\\alpha j}$ with the affine pieces $A_{\\alpha k}$. The affine-fibre-product leaf gives affineness, while the fibre-product universal property and base-change of open immersions place them inside the required base changes over $W$; their images cover each $A_{\\alpha k}$, hence $W$. Step 5 matches these finite refinements and the weakly-etale check against the exact covering condition in `sk-def-pe-site`.

I checked empty schemes and empty affine pieces, singleton covers, repeated indices, and the case $W\\subseteq U_\\alpha$. All unions remain finite, and no local-Noetherian fact is used silently. Every non-elementary input appears in a step’s `uses`, each quote in `citations.json` is copied verbatim from that node’s statement, and the proof dependency list is the union of the uses. No statement error, duplicate, cycle, hidden definition, or off-route tool citation was found. No Lean file or compiler/build tool was used.
