# Q53 stage-1 report: lem-coef-labelled-spine-prism-horn-calculus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-labelled-spine-prism-horn-calculus.json`: existing item proof retained and audited; status set to `split`; no new nodes.
- `citations.json`: 14 exact statement quotes covering every cited node in every proof step.
- `report.md`: this report.

## Attachments

None. I searched the project Lean source and the upstream reference for the item id and its defining terms; no sorry-free declaration states this item exactly.

## WANTED

- `https://arxiv.org/html/2311.13362v1`, Definitions 6.1–6.2, Proposition 6.4, Corollary 6.5, Definition 6.7, Proposition 6.9, Proposition 7.1, Corollaries 7.2, 7.4 and 7.5 (the source is online and is not archived in `literature/`).

## Review by Q53

I read the item node, its blueprint ancestor `prop-coef-integral-exceptional-adjoint`, the `sk-prop-sf-biduality-general` unit, and the full statement of each dependency in `proof_deps`. The dependency statements are the ones quoted verbatim in `citations.json`; no step relies on a proof detail that its cited statement does not provide. The item remains in the generic small monoidal infinity-category setting of `def-coef-segal-presheaf-localization`, with no coefficient-category or scheme hypotheses silently added.

Step 1 uses `lem-coef-space-universal-colimits` for pullback colimits, `lem-coef-infinity-yoneda-presheaf-limits` for objectwise presheaf colimits, and the Segal-localization definition for cartesian label transport; these give the represented pullback-face calculation. Steps 2–5 give the ordinary finite combinatorics: step 2 uses objectwise colimits, while steps 3–5 spell out the paired-cell strong induction, exact attaching intersection, exhaustion, and transport to labelled horns. I checked the base cases n=0,1,2 and the first nontrivial case n=3, i=1; all attached horns have dimension strictly below n.

Step 6 uses the Yoneda-presheaf limits, finite-poset Kan-extension, and cofinality-test statements to compute the boundary as the finite colimit of proper labelled faces. I checked the empty m=0 boundary and the two-vertex m=1 boundary, and verified that the posets used for each non-surjective simplex have an initial element and contractible nerve. Step 7 uses the ordinary inner-anodyne pushout-product leaf, the small-object cell-factorization leaf, the simple-inner-anodyne base-change statement, and the cofinality test. Their hypotheses (small horn family, degreewise injective boundary, representability of every simplex pullback, and equivalence of the adjoint projection) are explicitly established in the step or cited statement. Step 8 computes the labelled representable pullback and its projection, then applies the simple-map criterion; I checked the k=0 case as well as positive dimensions. Step 9 is the direct reassociation of pointwise pullbacks and pushout gluing. Step 10 checks the unit-label vertex formula using the empty-tensor convention and records the factor-symmetry argument without asserting maps from arbitrary objects to the unit.

The proof dependencies equal the union of the step uses, the blueprint `from` location points to the labelled-horn portion of the exceptional-adjoint proof, and `same_as` is empty after searching the whole DAG and blueprint. The four fresh `msearch.py` records (LeanFinder, LeanSearch, Loogle, and Mathlib grep) found only ordinary simplicial-set or unrelated categorical declarations; none is a one-line Mathlib match for the labelled presheaf result. No statement error, duplicate, cycle, SGA citation, or unrecorded non-elementary fact was found, and no new node was necessary.

## What was wrong or corrected

The shared item was already reviewed and mathematically complete but still marked `unsplit`. I changed only the copied sandbox item status and worker split metadata, refreshed its search records to the searches actually run by Q53, and supplied the required citations and report. No statement or proof step was weakened.

## Unfinished

Nothing remains for this item before delivery.
