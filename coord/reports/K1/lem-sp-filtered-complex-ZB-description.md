# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-ZB-description.json`: statement, split proof, status `split`.
- `dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-associated-spectral-sequence-construction.json`: statement-only unsplit node; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. The item was unsplit and had no Lean declaration. I read the complete source proof of Stacks Homology Lemma 12.19.2 (Tag 012K) in `/home/ubuntu/c1-stacks-review/homology.tex`, including the preceding differential-object self-map construction. The existing DAG had no node for that construction, so I added one generic statement-only node rather than restating the item's concrete formulas. The item statement and its `def-sp-abelian`, `def-sp-filtration`, and `def-sp-spectral-sequence` dependencies were retained and the source path/place was kept as the imported Stacks source.

## Review by K1

I checked the item against Tag 012K and read the parent blueprint step in `thm-sp-spectral-object-yields`. Step 1 cites the new construction node for exactly the graded differential object, injective filtration shift, page bidegree, and initial graded object. Step 2 cites that construction and the filtration definition; it unwinds the source's kernel/image formulas and separately verifies inclusion using `d^2=0` and filtration stability. Step 3 uses the quotient-filtration statement and writes the representative calculation identifying the cohomology image with `Z_r/B_r`; no hidden map is taken from a cited proof. Step 4 checks the `r=1` cycles/boundaries specialization and uses finite filtration tails for stabilization. I checked the hypotheses at each use: the category is abelian, the filtration is decreasing by subcomplexes, and boundedness supplies the eventual endpoint terms. I also checked small cases: for a zero differential, `B_r=0` and `Z_r=gr^pK`; for a two-term complex with the identity differential, the `r=2` quotient and image both vanish. No duplicate node was found by DAG keyword/tag searches or blueprint search, and all Mathlib searches were run and recorded as issued by `msearch.py`.

5. Nothing remains unfinished in the split; the required dry run is the next check.

## Not duplicates

lem-sp-filtered-complex-associated-spectral-sequence-construction vs lem-sp-filtered-complex-ZB-description: the new node only states the generic graded differential-object construction and its initial page; the item states the explicit componentwise $Z_r/B_r$ formulas, their cohomology-image interpretation, the $r=1$ homology identification, and stabilization.

## Second reading by K1

- Item statement: checked against Stacks Homology Lemma 12.19.2 (label `lemma-spectral-sequence-filtered-complex`, Tag 012K) and the parent blueprint; formulas, bidegrees, quotient-complex image, $E_1$ identification, and finite-filtration stabilization agree under the stated hypotheses.
- Step 1: checked against Definition 12.18.1 and Remark 12.18.2 and the cited construction node; the graded object, inclusion, initial page, and bidegree are exactly what the cited node states.
- Step 2: checked against the self-map formulas in Remark 12.18.2 and the filtration definition; the displayed kernels/images and $B_r\subseteq Z_r$ follow from the cited statements and $d^2=0$.
- Step 3: checked directly in the two quotient complexes; representatives, coboundary changes, and the image quotient give exactly $Z_r/B_r$, with the abelian-category and filtration definitions now cited.
- Step 4: checked the $r=1$ specialization and finite-filtration tails; the differential is the graded differential, and both displayed subobjects stabilize for fixed bidegree.
- New node `lem-sp-filtered-complex-associated-spectral-sequence-construction`: checked against Definition 12.18.1, Remark 12.18.2, and the parent construction; self-contained statement-only node, definitions cited, no duplicate found by DAG/tag/keyword search, and recorded Mathlib searches are genuine no-match or unavailable results.
- Changes: replaced the undefined “bounded” filtration wording with the defined “finite” filtration; added `def-sp-abelian` to the quotient-image and stabilization step dependencies; removed the new node's blueprint `via` self-reference; updated `proof_deps` accordingly.
- Edge cases checked: zero complex and zero differential give $B_r=0$ and $Z_r=\operatorname{gr}^pK$; a two-term identity-differential complex has the expected vanishing higher quotient; empty index tails stabilize under finite filtration.
