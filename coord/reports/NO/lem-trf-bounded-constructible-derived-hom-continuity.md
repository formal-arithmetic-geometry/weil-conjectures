1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-bounded-constructible-derived-hom-continuity.json`: statement node split with four proof steps; no new nodes, hence no Mathlib leaves.

2. Attachments: none.

3. WANTED: none.

4. I checked the item against its source text in the current DAG and against the chapter `sec-trace-formula` and unit `sk-i-curve-zero`. The existing node `lem-trf-constructible-etale-ext-continuity` supplies the sheaf-level Ext comparison under exactly the same inverse-system, finite-ring, and constructibility hypotheses. I searched the whole DAG and blueprint before deciding that no new helper node was needed: the exact Hom sequences for distinguished triangles, exactness of filtered colimits of abelian groups, the five lemma, exact module inverse image, and derived inverse-image coherence are already stated by cited nodes.

## Review by NO

I read the full statements of the item, `lem-trf-constructible-etale-ext-continuity`, `def-weil-t-structure`, `def-weil-pbc-derived-categories`, `def-weil-pbc-bounded-derived-subcategories`, `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-hom-out-of-triangle-exact`, `lem-weil-pbc-hom-into-triangle-exact`, `lem-weil-pbc-filtered-colimit-abelian-groups-exact`, `lem-weil-pbc-five-lemma`, `lem-weil-pbc-derived-inverse-image-composition`, and `lem-weil-pbc-ext-exact-functor-composition-comparison`. Step 1 uses the sheaf Ext isomorphism for nonnegative degrees, standard t-structure orthogonality for negative degrees, exactness of inverse image to preserve module hearts, and the derived-category shift identification; all four cited statements say those facts. Step 2 fixes a shifted constructible target, forms the five-term Hom ladder for a source triangle, uses the cited Hom exactness statements and filtered-colimit exactness, and applies the five lemma. The bounded t-structure and bounded-derived-category statements supply the finite Postnikov tower with constructible cohomology sheaves. Step 3 repeats the same ladder argument in the target variable and performs the second finite Postnikov induction. Step 4 checks that exact inverse-image functors, their derived composition coherence, and the Ext functoriality formula propagate composition, shifts, and later-stage compatibility through the natural truncation triangles. I checked the edge cases of a single sheaf, a zero complex, a one-term shift, and a triangle with a zero endpoint; the inductions reduce to the sheaf Ext comparison in each case. Each step is a single routine argument and does not hide a separate lemma. No statement or source hypothesis was changed.

5. Nothing remains unfinished.
