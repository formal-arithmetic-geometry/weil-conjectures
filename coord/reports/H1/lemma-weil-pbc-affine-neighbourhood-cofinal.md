# Delivery report: lemma-weil-pbc-affine-neighbourhood-cofinal

1. **Files written**

- `dag/nodes/sec-curve-estimates/lemma-weil-pbc-affine-neighbourhood-cofinal.json`: split item; no new nodes.

2. **Attachments**

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for affine-neighbourhood/cofinal/pointed-etale notions and for the blueprint tag. No sorry-free or sorry-bearing declaration states this item exactly. The source does contain related declarations such as `AlgebraicGeometry.Scheme.Hom.Chart.nonempty` (AlgebraicGeometry/Morphisms/Finite/Chart.lean:56-64), but that is only the affine-chart existence lemma and is not an exact declaration of cofinality.

3. **WANTED**

None. The cited Stacks sources are already represented by existing DAG nodes.

4. **Review notes**

The imported one-step sketch was expanded into three source-cited steps. Existing nodes `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`, `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and `lem-weil-pbc-colimit-initial-full-subcategory` state the affine refinement, ambient cofilteredness, and initial/full-subcategory colimit criterion respectively. The proof therefore does not create duplicate nodes. The item now has `status: split`, a document-based proof origin, and `same_as: []` after a whole-DAG blueprint search.

5. **Checks and unfinished work**

`python3 tools/review_split.py lemma-weil-pbc-affine-neighbourhood-cofinal` passes. `python3 tools/check_dag.py` cannot complete because the existing DAG contains an unrelated missing dependency `lem-weil-pbc-qcqs-fibre-product-gluing`; no file for that node was created or changed here.

## Review by H1

The sources checked were Stacks `etale-cohomology.tex`, proof of Lemma Tag 04HX, and Categories Lemmas Tags 0BUC and 04E7. The item agrees hypothesis by hypothesis with the existing affine-shrink, pointed-neighbourhood cofilteredness, and initial-full-subcategory nodes. Step 1 uses the affine-shrink statement exactly. In repaired step 2, nonemptiness of each comma category comes from step 1; connectedness is checked using the fibre-product and equalizer clauses in the cofilteredness statement, followed by an affine shrink and fullness of the affine subcategory, which supplies the required zigzag. This explicitly establishes the meaning of initial used in the item. Step 3 uses the opposite-category finality and colimit comparison stated by the initial-full-subcategory node. The statement introduces no unsupported objects beyond its two definition dependencies. Whole-DAG searches found no duplicate node or exact source declaration. No new statement edge case was required because no new node was created; affine shrink was checked for `W = V` and for an affine ambient neighbourhood. The returned correction was the missing comma-category argument and the inaccurate delivery paragraph; both are repaired here.

