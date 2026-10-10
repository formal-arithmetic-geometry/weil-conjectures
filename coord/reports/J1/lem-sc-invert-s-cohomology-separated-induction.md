1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-separated-induction.json`: item, statement node, split; no new nodes and therefore no Mathlib leaves.
- `citations.json`: four verbatim citations for proof step 1.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The item was unsplit, and no matching declaration or blueprint node was found. The existing DAG already supplied every supporting fact needed by the first paragraph of Stacks Lemma 08DR, so creating duplicate nodes would have violated the existing-node search requirement.

5. Unfinished

Nothing remains unfinished.

## Review by J1

I read the item source, Stacks `coherent.tex`, Lemma 08DR (`coherent-lemma-induction-principle`), first proof paragraph, and checked the statement against its hypotheses: the ambient scheme is quasi-compact and quasi-separated, the property is on quasi-compact opens, the affine case and the three-open gluing premise are assumed, and the conclusion is restricted to separated quasi-compact opens. I also searched the slopmaster2 Lean source for the item id, the 08DR label, and the relevant induction phrases; no declaration exists.

Step 1 cites `lem-weil-pbc-qcqs-finite-affine-open-cover`, whose statement gives a finite affine cover; `lem-weil-pbc-separated-affine-open-intersection`, whose statement gives affine pairwise intersections and the finite affine cover of the overlap; `lem-weil-pbc-separated-cancellation`, whose clause (a) says an open immersion is separated; and `lem-weil-pbc-proper-fp-permanence`, whose clause (e) says a composite of separated morphisms is separated. These statements exactly support the finite-cover setup, quasi-compact overlap, and separatedness of the two subopens. The remaining finite-union and induction bookkeeping is elementary. Step 2 is marked elementary because it is the finite induction itself: the n = 1 case is the affine premise, and for n > 1 the previously established separated quasi-compact subopens satisfy the induction hypothesis and the stated gluing premise.

I searched the whole DAG and blueprint for the item, 08DR, separated quasi-compact induction, finite affine covers, and affine intersections before editing; the four cited support nodes already exist, and no new node is needed. I checked the small cases n = 1 (an affine open) and n = 2 (two affine opens in a separated scheme, with affine overlap). The item blueprint `from.place` remains the exact 09MR/08DR first-induction clause, and the split report records that route.
