# Stage-1 delivery: lem-pur-compact-support-roos-cofinality

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-compact-support-roos-cofinality.json`: split the item into seven explicit calculation steps; statement unchanged. Added the existing `def-pur-sheaf-tensor-product` to `stmt_deps` for the tensor notation already used in the statement.
- `citations.json`: verbatim statement excerpts for every step/node citation (including a second excerpt for the shifted-cone convention).
- `report.md`: this report.

## New nodes

None. In particular, the inverse on the kernel, the cone contraction, and the dual-basis tensor inverse are actual formulas checked inside the proof, rather than new nodes restating the cofinality or scalar-comparison clauses. The checks use finite telescoping sums, two-by-two differential formulas, and the defining description of cohomology. There are no new Mathlib leaves.

## Attachments

None. Searched the whole `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` tree for the exact blueprint id, Roos, cofinality, subsequences and homotopy limits. Read `CategoryTheory/Triangulated/HomotopyLimit.lean` and the context in `SixFunctors/ClosedImmersionStages.lean`. Their results concern abstract Milnor triangles and closed immersions; neither gives the specified block-sum map on strict complexes, its composition normalization, and its finite-free scalar comparison. Ordinary inverse-system or generic cone declarations do not attach this item.

## WANTED

None. The item is explicitly agent-formulated and the proof is marked `proof_origin.by = agent`. Stacks Tag 0941 is context for the Roos complex, not a claim that Stacks states this explicit block-map result.

## Audit of the imported material and route

There was no imported proof: the item was an unsplit auxiliary of Q134's integral coefficient comparison. Its statement is true as written. The exact-countable-products assumption is retained, although the explicit chain homotopy equivalence below does not need it. No transition is assumed surjective or invertible, and the argument does not require boundedness, enough points of the site, or any interchange of sheafification and infinite products.

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-thm-sf-compatibility.json`, the current blueprint `main-20261015/.../thm-pur-rational-and-qbar-purity.proof.md` (Step 2), and the parent item's proof and source metadata. The original ancestry is retained through `lem-pur-compact-support-integral-coefficient-comparison` and `lem-pur-adic-purity-scalar-naturality`. This supplies the block-map auxiliary used in the parent's Step 5 and in coefficient compatibility, clause (7) of the current compatibility unit. It does not replace any geometric proof route, and the item is not the unit's key statement, so no unit realization file changes.

Searched the whole DAG and `tools/blueprint_refs.py search` for Roos and cofinality; the blueprint has derived-limit definitions and comparisons but no node giving the stated explicit cofinal block map. `blueprint_refs.py ancestor` confirms `thm-pur-rational-and-qbar-purity`. `same_as` remains empty. No new node, same-tag pair or off-route statement citation is introduced. The proof cites only existing definitions, and all their statements were read.

The item's inherited Mathlib searches from Q134 are preserved as historical records. I separately ran and read eight searches with `msearch.py` under this item's own sandbox: two LeanFinder phrasings, two LeanSearch phrasings, Loogle `"homotopyLimit"` and `"Roos"`, and grep for the explicit Roos notion and for `invLimEquiv|pEquivOnLim` in Order. Those commands and their actual results are recorded in `searches.jsonl` and appended to the item. I read `Order/DirectedInverseSystem.lean` at 379 and 479 and `CategoryTheory/Limits/Shapes/SequentialProduct.lean`: the first gives ordinary type-valued limit equivalences, and the second realizes infinite products as sequential limits of changing finite prefixes. Neither is the strict-complex block map here. Generic mapping-cone, Dold--Kan and quasi-isomorphism hits do not state the item. All eight services/searches completed; no unavailable search was described as a negative result.

## Unfinished work

None at stage 1. No Lean was written, compiled or built. The next stage may implement the displayed maps directly; no additional unsplit lemma is hidden behind a reference to cofinality or exactness of products.

## Review by Q113

I read Stacks `sites-cohomology.tex`, Tag 0941, label `lemma-derived-limit-is-ok`, including its proof. It computes the derived inverse limit using K-injective towers and a product cone; it does not assert the explicit block-sum comparison. I therefore wrote and checked the direct chain calculation rather than cite that tag as a cofinality theorem. For the scalar clause I read `sites-modules.tex`, Tag 03EK, `section-tensor-product`, including its sectionwise definition and sheafification, and `algebra.tex`, Tag 00CX, `lemma-tensor-product`, its universal property and generation by pure tensors. I checked all three tags against `literature/stacks-project/tags/tags`. No SGA source is used and no document was downloaded. There are no new-node sources to review.

For Step 1 I read `def-weil-inverse-system` and `def-weil-abstract-derived-category`: the former explicitly gives the composite transition law and the latter gives the cone matrix and shift sign. Reordering the shifted-cone coordinates and negating the old first coordinate gives exactly `(dx, Dx-dy)`. I checked cancellation in `b_e D = D_e a_e`, so the named map is a chain map with the requested sign, rather than just some abstract isomorphism of its domain and codomain.

For Step 2 the same inverse-system statement supplies every `T(i,j)` used. The least retained index greater than or equal to `i` exists because `e >= 1`. The section extends backward from that index. I checked `a alpha = b beta = 1` and `D alpha = beta D_e` separately at retained and nonretained coordinates, including `1 <= i < e`. This corrects the tempting but wrong approach of discarding the initial block when constructing an inverse.

For Step 3 I read the full statement of `def-weil-sheaf-of-modules-category`, which says that kernels are computed sectionwise, and used the transition composition statement again. On each finite interval ending at the next retained zero, the inverse is the displayed backward sum. At its retained left endpoint the missing equation is exactly `b_e y = 0`. At the initial interval there is no retained left endpoint and thus no extra constraint. I checked both composites of this inverse explicitly; this establishes a genuine isomorphism between the two kernels, with no assumption on the transitions.

For Step 4 the cohomology and quasi-isomorphism definitions come from the quoted part of `def-weil-abstract-derived-category`. I computed `d h + h d = 1` on both kernel coordinates; the internal differential terms cancel because the backward-sum map is a chain map. The already constructed chain section lets `1-jr_e` land in that kernel. I then checked `d H + H d = 1-jr_e`. For a cycle the difference is the actual boundary `d H z`, so the inverse on cohomology follows from the definition of `ker d / im d` without invoking an uncited long exact sequence or homotopy-invariance theorem. These are sheaf-morphism identities and remain valid without a site with enough points.

For Step 5 I used precisely the componentwise transition equation in `def-weil-inverse-system`. The double finite sum runs through disjoint consecutive blocks from `efk` to `ef(k+1)-1`, and the two transitions multiply to `T(efk,i)`; this proves strict composition for the specified maps. I checked the augmentation on its actual pair of coordinates, which leaves a zero shifted component. Naturality is the same finite transition identity applied to a tower map.

For Step 6 I read the statements of `def-weil-pbc-constant-sheaf`, `def-pur-sheaf-tensor-product`, and `def-weil-pbc-module-tensor-product`. They define, respectively, sheafified constant coefficients, sheafified sectionwise tensor, and the tensor universal property with pure-tensor generators. The finite-basis maps are mutually inverse by the two dual-basis equations. The relation on arbitrary constant-sheaf sections is obtained by sheafifying the original equality of constant presheaf maps, so I did not assume that sections of a constant sheaf are constant. A second explicit inverse uses one product for each of the finitely many basis coordinates. Its sum has only the basis rank many terms. This proves invertibility without falsely asserting that sheafification commutes with infinite products. The choice of basis proves that the already canonical map is invertible; it does not define that map.

For Step 7 the same two tensor definitions give the generator test for all equalities. I checked the internal differential, the shift sign, `1-s`, finite direct sums, and both coordinates of `r_e`. The displayed finite-sum identity proves commutation with `b_e`, not merely with the projections `a_e`. Multiplication in the second factor proves B-linearity of the canonical map; hence its inverse is B-linear as well. The zero second coordinate verifies the augmentation normalization after extension of scalars.

I tested the statements and calculations at `e=1` (all maps are identities and both kernels vanish), the zero tower, constant towers with identity transitions, and towers with zero transitions (the retained/nonretained calculation works without surjectivity). I also checked `e=2` in the first initial index: `c(y)_1=y_1`, with the first retained equation `y_2=-t_2 y_3` imposed by `b_2 y=0`. Composition for `e=2,f=3` groups exactly the six original terms. Tensor ranks zero and one give the zero and identity comparisons. No completeness, flatness or quotient-ring hypothesis is smuggled into these general statements.

Against delivery-errors B--E: all objects in the original statement are introduced; the tensor notion now has its definition dependency; every step has exact existing citations, boolean `elementary`, source and complete computation; `proof_deps` is their union. Every elementary label denotes the displayed substitution/telescoping or matrix identity, not an appeal to a standard theorem. There are no new nodes to be duplicates, item clauses, or unsearched leaves. The item statement is unchanged, there is no statement dispute, and no cycle can come from the newly added definition dependencies. Each step is below 2000 characters (maximum 1276), and I also read them for hidden lemmas: the kernel inverse, homotopy and tensor/product inverse are all written out, so no unproved comparison or standard identification is left inside a long paragraph.
