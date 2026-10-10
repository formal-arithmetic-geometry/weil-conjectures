# Stage-1 delivery: lem-sc-tensor-section-affine-open

Files written: dag/nodes/sec-curve-estimates/lem-sc-tensor-section-affine-open.json (item, statement node, split; existing Mathlib search says no match). No new nodes and no Mathlib leaves.

Attachments: none. A search for the item id and the tensor-section/affine-open notions in the read-only Lean source found no declaration stating this item exactly.

WANTED: literature/stacks-project/varieties.tex, Lemma 09NC proof, for lem-sc-tensor-section-affine-open. The local Stacks checkout is absent. I read the Stacks project page at https://stacks.math.columbia.edu/tag/09NC instead.

WANTED: literature/stacks-project/properties.tex, Lemma 01PV, for the affine-intersection step. I read https://stacks.math.columbia.edu/tag/01PV instead.

WANTED: literature/stacks-project/modules.tex, Lemmas 01CT, 01CB, and 01CY, for the fibre calculation. I read the 01CT and 01CY pages on the Stacks site and the existing cited node's 01CB fibre formula.

The item was unsplit. Its statement already names the necessary notions and agrees with the tensor-section subargument of 09NC and its cited 01PV. Its TeX is encoded once in JSON; the apparent doubled backslashes in JSON displays are ordinary escaping. The blueprint ancestor reference is specific, and a whole-blueprint search for "tensor section affine" and "nonvanishing locus" found no duplicate. The unit is sk-thm-curveestimate; this item lies below its previously realized statement and does not change the unit record.

## Review by F1

I read the item's 09NC proof sentence and the 01PV statement and proof on the Stacks site, then read all three cited node files. Step 1 takes exactly the fibre identity for tensor sections, including invertibility and one-dimensional fibres, from lem-weil-pbc-invertible-pullback-tensor (its clauses (1) and (3)). It takes the equivalence between a nonzero fibre value and membership in the nonvanishing locus from lem-weil-pbc-nonvanishing-section-trivializes. The remaining calculation is elementary linear algebra: choose a basis in every one-dimensional fibre, so the tensor coordinate is the product of scalar coordinates. This proves the equality pointwise, including when a factor section vanishes.

Step 2 takes from lem-sc-affine-cap-section-open precisely that an affine open intersected with the nonvanishing locus of a section of an invertible module is affine. Starting at the assumed affine X_tj, induction over the remaining finite indices preserves affineness, and step 1 identifies the final open with X_tau. The hypothesis of 01PV is checked at each induction step: the current U is affine, each L_i is invertible, and t_i is global. The two general invertible-module nodes are declared as tool uses because their unit differs from this item's and this unit supplies neither fibre formula nor the nonvanishing criterion.

I checked B1-B9 and C1-C8 against the files: no new node is needed, every cited statement contains the fact taken from it, each non-elementary step names its nodes, and the proof does not use the proof of a cited node. The 09NC route and the tag 01PV are preserved, with no claim about intersections of arbitrary affine opens. For D1-D5, neither step restates the item or hides the finite iteration. For E1-E7, the hypotheses used are present. Small cases: for one factor the equality is immediate and the affine conclusion is the hypothesis; on X=Spec(R) with trivial line bundles and sections f_i, the locus is D(product f_i)=intersection of D(f_i); a zero section gives the empty affine open; the empty scheme gives empty opens. I corrected the draft's unnecessary concern about TeX escaping after opening the actual file, and added the explicit finite induction and exact citations. The local TeX source absence is recorded above.

What remains: no proof obligation is left in this item. The cited DAG lemmas may still be open in later stages.
