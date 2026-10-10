# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-topological-leray-spectral-sequence.json` — statement, split; no Mathlib match.
   - `dag/nodes/sec-curve-estimates/lem-sc-topological-pushforward-injective.json` — statement-only child; no Mathlib match.
   - `citations.json` — verbatim statement excerpts for every cited node in every proof step.

2. Attachments: none.

3. WANTED: none. The Stacks source is present in the project citation inventory; the source text itself is not checked out in this clone, so the split follows the recorded labels and the existing imported statements.

4. Problems found: the item was unsplit and had no matching declaration in `WeilConjectures/`. The existing child `lem-sc-leray-closed-pushforward-cohomology` uses this item, but does not state the general spectral-sequence construction. The imported abstract theorem `thm-sp-grothendieck` gives the derived-functor spectral sequence, while `thm-sp-double-complex-spectral-sequences` supplies the explicit page, stabilization, filtration, and functoriality clauses. A separate statement-only node was necessary because no existing DAG or blueprint node stated that topological direct image preserves injectives. Blueprint searches for “direct image injective”, “inverse image exact”, and “Leray spectral sequence” found no exact topological injective-pushforward node; the only Leray result in another form was the scheme/quasi-coherent `pqf-lem-leray`.

5. What remains: no proof was left incomplete. The new injective-pushforward node is intentionally statement-only for the next stage.

## Review by C1

I read the item source label `literature/stacks-project/cohomology.tex`, Lemma 01F2 (`cohomology-lemma-Leray`), and checked the imported abstract sources named by the split: `thm-sp-grothendieck` (the composable left-exact functor theorem) and `thm-sp-double-complex-spectral-sequences` (double-complex pages, differentials, convergence, finite image filtration, stabilization, and functoriality). The item statement agrees with the Leray statement hypothesis by hypothesis: a continuous map of spaces, an abelian sheaf, sectionwise direct image, right derived direct images, first-quadrant pages, the `E_2` term, convergence filtration, functoriality, and the edge map. The child statement is the exact adjunction input used in the Leray proof: inverse image is exact and left adjoint to direct image, hence direct image takes injectives to injectives.

Step 1 cites `def-sc-topological-abelian-cohomology` for the abelian sheaf categories, enough injectives, and derived global sections, and `def-sp-left-exact-additive` for the left-exact/additive functor notion. The direct-image left exactness is sectionwise and the hypotheses are explicit. Step 2 cites the new child for preservation of injectives and `lemma-weil-pbc-leray-acyclicity` for the statement that injectives are acyclic for a left exact additive functor; this is declared as a generic tool use because it belongs to another unit. Step 3 cites `thm-sp-grothendieck` for the `E_2=R^a\Gamma(X,R^bf_*F)` spectral sequence and `def-sc-topological-abelian-cohomology` for identifying derived global sections with `H^a`; the composite is identified sectionwise by `\Gamma(X,f_*G)=\Gamma(Z,G)`. Step 4 cites the construction clause of `thm-sp-grothendieck`, the explicit double-complex theorem, and `def-sp-filtration`; these statements provide the bidegree `(r,1-r)` differential, kernel/image page transition, stable `E_\infty`, finite decreasing filtration, graded-piece identification, and functoriality. Each citation quote in `citations.json` was checked as a verbatim substring of its cited statement.

I checked edge cases `n=0` (the edge map is the identity on global sections), `f=id` (the spectral sequence has only the direct-image row), and `F=0` (all pages and the filtration are zero). The child statement was tested on `f=id`, the map from the empty space, and a map to a one-point space; the adjunction and injective-preservation conclusions remain correct in each case. No source statement was weakened or silently changed.
