# Stage-1 report: lem-sp-nilpotent-action-koszul-unit

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-nilpotent-action-koszul-unit.json: statement node, now split into seven steps; statement and stmt_deps retained verbatim. The required Mathlib searches found generic homology and completion ingredients, not the full assertion.
- citations.json: one verbatim statement quotation for each node used in each proof step.
- report.md: this report. searches.jsonl retains the actual queries and returned names. prepare.py is sandbox-only preparation work, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. Two existing Mathlib leaves supply the short-exact-sequence triangle and the splitting of a triangle whose third map is zero.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag, nilpotent, Koszul, and completion. No project declaration states every clause, including the specified zero-shifted-coordinate map and its strict naturality. General nilpotent-ideal Tor-amplitude tests and the principal-completion modules do not do so. Existing sorry declarations are not attachments.

## WANTED

None. All sources needed for this item are present locally.

## Issues and corrections

The input statement is correct with its stated right-tensor and reordered Roos conventions. It had no proof steps. I retained every hypothesis and clause and supplied the argument, in particular the sign on the quotient map to Q[1]. It is not legitimate to omit that sign or to split the original short exact sequence as towers: the displayed sections are only degreewise maps of sheaves. The proof states this explicitly. No assertion about arbitrary sheaf epimorphisms being sectionwise surjective is used.

The unit and chapter records were read; this node supplies only the nilpotent-action calculation in the completeness sentence of sk-lem-sp-tower. It is not the key node of that unit, so neither record was changed. The separate double-Roos interchange in the parent is not part of this item.

## Not duplicates

No new nodes were created. Whole-DAG statement searches for Roos, nilpotent towers, constant towers, short exact sequences and zero-third-map splitting located the existing tools used here. Whole-blueprint searches with tools/blueprint_refs.py for nilpotent, constant tower, Koszul, completion and short exact found no other blueprint statement equal to this item. Its blueprint.same_as remains []. Its existing precise from.place and ancestor sk-lem-sp-tower were retained. No search-only candidate was made into a node.

## Proof and source audit

Read the current blueprint's sk-lem-sp-tower/_section.md and sk-lem-sp-tower.proof.md, Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.12 (the proof of (1) iff (2)), Stacks 012Z / homology-definition-associated-simple-complex in homology.tex, and Stacks 0941 / sites-cohomology-lemma-derived-limit-is-ok in sites-cohomology.tex. Bhatt--Scholze gives transition x on the first cone factor and identity on the second; after right total tensor this is (1,t) on the ordered (x,y) summands. Stacks 012Z fixes the tensor signs; 0941 explains the derived-limit model. The finite-sum contractions are an explicit refinement written here, so proof_origin.by is agent, not a claim that the printed source contains these formulas verbatim.

Read the statements of all seven different cited nodes, including their hypotheses and conventions. The three module/derived/complex definitions establish the coefficient category and signs. def-weil-strict-roos-model defines diagonal product maps and the cone coordinates. lem-weil-strict-roos-comparison states precisely the natural isomorphism to the total derived inverse limit and the normalization for a strict augmentation; it is not merely a triangle-existence claim. The Mathlib leaves lem-weil-pbc-degreewise-split-derived-triangle and lem-pc-derived-zero-third-split give the exact triangle and the compatible biproduct isomorphism used below. I also read their matching Mathlib declarations: HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit at DegreewiseSplit.lean:253, the DerivedCategory Qh triangulated instance at DerivedCategory/Basic.lean:173, and CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang at Pretriangulated.lean:579. The reported matches are generic tools already in the DAG, not new leaves.

## Review by Q22

For step 1 I checked the tensor definition's actual differential, not just its title: the sign on t^j is (-1)^(k+1) because the source is Q^(k+1) tensor L^(-1). The shift convention in def-weil-abstract-derived-category makes the quotient differential -d_Q; therefore p^k(x,y)=(-1)^k y is required. The displayed degreewise section proves surjectivity and identifies the kernel, without flatness of Q or regularity of t. The principal Koszul definition supplies the actual complexes and transitions. This proves the first clause rather than outsourcing it to another copy of that clause.

For step 2 I verified d a_j = a_j d using t^j t = t^(j+1), and p_j a_j = t p_(j+1). These equations give the tower maps and levelwise exactness. The Koszul definition says transitions are (t,1) on degrees (-1,0); these become (1,t) on the reordered total-tensor summands. The sections are not required to respect those transitions.

For step 3 I opened the Roos definition and compared its original (y,z) coordinates with the item's reordered (v,u): the differential is indeed (dv,-du-(1-s)v), and strict maps apply the product map on each factor. Products of the explicit degreewise sections give sections on products. Their biproducts give a degreewise split short exact sequence of Roos complexes. This elementary construction does not require a hidden theorem about exactness on sections.

For step 4 I checked s_Z^r=0 from the termwise hypothesis in every degree. The finite geometric sum A is a two-sided inverse of 1-s_Z and commutes with d. Substituting h(v,u)=(-Au,0) into the actual differential gives dh+hd=1 with exactly the displayed signs. This proves acyclicity on the complex itself. The cited strict Roos comparison explicitly identifies this complex with the specified total derived inverse limit; all of its smallness, coefficient and exact-countable-product hypotheses are present. Its use is declared in split_report.tool_uses because it is a generic off-unit normalization tool, not an alternative reconstruction route. No common exponent across an outer tower is used here.

For step 5 I verified both telescoping identities fB=1 and Bf=1-Delta pr_1, starting at index 1. Each component of B is a finite sum, hence a global sheaf morphism; no infinite sectionwise sum is assumed. The identity dH+Hd=1-delta e and e delta=1 prove that this specific diagonal augmentation induces an isomorphism on cohomology, including in negative degrees. This is a short coordinate argument and does not warrant a separate node for a clause of the item.

For step 6 I checked the hypotheses of the existing degreewise-split triangle leaf against the explicit Roos sequence, and read the zero-third-map splitting leaf's compatibility e u = inclusion. Acyclicity makes its third derived object zero, so the connecting map is zero; the compatible biproduct inclusion has the first projection as inverse. Factoring cohomology through localization then proves the chain map Roos(i) is a quasi-isomorphism. The equality Roos(i) delta = u_Q follows on both coordinates, so the argument proves the specified map rather than just some isomorphism of the two objects.

For step 7 I checked the formulas for b tensor 1 and for the Roos functor on strict maps. These give the naturality square strictly, including when source and target have different nilpotence exponents or no nilpotence at all. The exponent occurs only in the proof of quasi-isomorphism, not in u_Q. Applying this to each outer transition proves the final strict-tower clause.

I tested t=0 (r=1, so A=1), Q=0, a complex in one degree, nonzero differentials, and Q with nonzero terms arbitrarily far in both directions. The two contractions still apply. For t a unit the annihilation hypothesis forces Q=0, which is consistent. Distinct outer exponents require no compatibility of contracting homotopies because the natural unit itself contains no exponent. No new statement needs a small-case test beyond the unchanged item. All steps are under 1000 characters; none exceeds the 2000-character long-step threshold or hides an additional comparison theorem. B1--B10, C1--C8, D1--D5 and E1--E7 were checked against the statements and sources as discussed above. No source error, statement correction, or additional definition was found necessary.

## Unfinished work

None in the mathematical split. This is stage 1 only; no Lean source was written and no compiler, Lake or build tool was run. The required server preflight and push follow this report.
