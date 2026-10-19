# Worker report: lem-trf-comparison-truncated-direct-images

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-comparison-truncated-direct-images.json`: existing statement node, now split in nine steps. Mathlib verdict: no matching truncated two-topology comparison. All inherited searches and metadata retained; five actual Q85 searches appended from the local log.
- `citations.json`: one verbatim statement quotation for each of the 24 step/node citations.
- `report.md`: this report. No new DAG nodes; no new Mathlib leaves.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the literal blueprint tag, the node id, truncated/direct-image terminology, weak Serre classes and comparisons of finer/coarser topologies. No project declaration states this item. The weak-Serre derived-subcategory file is general closure infrastructure, not the theorem here. Upstream master is reference material only; no master sorry was treated as a proof.

## WANTED

None. All mathematical sources used are in the supplied Stacks checkout.

## Findings and corrections

The imported item was statement-only, not an existing failed split. Its statement is correct, including its canonical map and the top degree. I kept it unchanged. Stacks 0EZA is formulated within Situation 0EZ3, whose fifth assumption is a covering-refinement hypothesis. The proof of this particular lemma never uses that fifth assumption; the item's hypotheses (1)-(4) suffice. In fact the argument uses chiefly (3), (4) and V_r; retaining the other stated assumptions causes no problem.

The source distinguishes the induction below r from the final degree, where the transgression d_(r+1) need not vanish a priori. The split records this distinction and proves the final exact sequence before sheafifying. It also explains why the target is the original E2 term, not an unspecified subquotient. For the source's final local-vanishing/sheafification assertion I used its own section-compare, Ad (3), injective-resolution calculation: exact fine sheafification of the pushed resolution recovers the original resolution. This gives zero in positive degrees in three equalities; no separate locality lemma or duplicate node is necessary.

The first finite-range isomorphism is proved using the other Leray spectral sequence rather than leaving the source's assertion that derived pushforward preserves a low-degree comparison unexplained. Its bottom edge is the map H^i(a_H), with the derived composition normalization made explicit. This is the same proof route through the commutative square and two Leray factorizations, and does not alter any unit step. The unit `sk-i-curve-zero`, chapter record, ancestry to `lem-trf-local-term-locality`, and its full via chain are retained. This item is not a unit's key statement, so no unit record is delivered.

## Searches and reuse

DAG source/tag and concept searches identified `sk-thm-groth-ss`, `sk-def-groth-ss`, `lem-sp-grothendieck-edge-maps`, the general site-localization lemma, exact sheafification, the exact-functor cohomology lemma, injective existence/preservation, and ringed-topos derived composition. I opened every cited statement. I specifically rejected `lem-kun-tensor-t-est` because it concerns schemes, not these arbitrary slice topoi, and rejected `lem-trf-slice-site-base-change-localization` because its hypothesis of all fibre products is stronger than the item's P-base-change hypothesis. The general `lem-weil-pbc-slice-site-localization` has precisely the needed continuous-identity-site-morphism hypotheses and does not need global fibre products. I also avoided the scheme-specific version of the higher-direct-image sheafification statement.

`tools/blueprint_refs.py ancestor` returns `lem-trf-local-term-locality`. Blueprint searches for `truncated higher` and `0EZA` found no duplicate imported blueprint node; the whole-DAG 0EZA search found only this item and its parent, which uses rather than states this theorem. No node was created. The two requested different semantic phrasings were run with LeanFinder, along with Loogle, Mathlib grep and LeanSearch, and their results were read. They returned topology/sheafification lemmas, generic derived comparison infrastructure, or an ell-adic comparison comment, with no exact theorem or one-line specialization. All five queries appear verbatim in `searches.jsonl` and the item's appended search entries. No unavailable service was recorded as a negative result.

## Not duplicates

No new nodes, hence no new/existing tag pairs. Every supporting fact was reused.

## Review by Q85

I read Stacks `sites-cohomology.tex`, Tag 0EZA (`lemma-V-implies-C-general`) statement and whole proof, `section-compare-general` including the square and hypotheses, and `section-compare` including its explanation Ad (3). I also read the local source passages for relative Leray 0734, derived composition 0D6E, site localization 03CF in `sites.tex`, exact sheafification 00WJ, and exact functors 010N in `homology.tex`. There are no new statements whose source or edge cases remain to be checked. The chapter/unit material and three-level route rules were checked as specified above.

Step 1 uses the actual universal property in `def-weil-pbc-sheafification` and the two exactness/limit statements in `lem-weil-pbc-sheafification-exact`. Fixing an already fine sheaf and identifying J_X H with the chosen H' are immediate universal-property calculations, with assumption (3) explicitly applied. The restricted-domain exactness is justified by kernels and colimits, not assumed just because a left adjoint exists.

Step 2 applies `lem-weil-pbc-slice-site-localization` to epsilon_Y and the object X over Y, so its inverse-image square really is the one used. The identity functor is continuous since a fine sheaf is a coarse sheaf; inverse image is the specified fine sheafification. `def-trf-geometric-morphism` gives the adjunction and finite-limit preservation, hence exact inverse image on abelian sheaves; `lem-sp-right-adjoint-preserves-injectives` supplies injective preservation. `lem-weil-pbc-site-sheaves-enough-injectives` applies because slices of the small supplied sites are small sites. `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` applies with constant integer rings, giving the actual natural normalized comparison. Its statement is for arbitrary small ringed topoi, not just schemes.

Step 3 uses the site-morphism specialization actually stated in `sk-thm-groth-ss`, the finite filtration in `sk-def-groth-ss`, and the bottom edge in `lem-sp-grothendieck-edge-maps`. The acyclicity hypothesis was verified in Step 2. I checked every incoming/outgoing index: an incoming differential at (i,0) starts at (i-s,s-1), and if that is in the first quadrant then 1 <= s-1 <= r. Thus all pieces that could affect degree i <= r vanish by the given V_r. The identification of the bottom edge with the augmentation defining a_H is made with the normalized common composite, not an arbitrary isomorphism of abutments.

Step 4 uses the same three cited statements with the pair (f_fine,epsilon_Y); the filtration in degree zero gives exactly the left edge isomorphism. This explicitly settles r=0. Step 5 cites no new fact: it substitutes the induction hypothesis into assumption (4), then uses S_Y J_Y = identity and V_r. Its objects really belong to A_Y before vanishing is used.

Steps 6 and 7 use the page homology formula from `def-sp-spectral-sequence`, the finite filtration from `sk-def-groth-ss`, and in Step 6 the left edge statement. The spectral sequence itself and differential bidegrees were established in Step 4. I checked all targets, including the outgoing page m+1, and all incoming arrows at (r+1,0). This proves the precise exact sequence in Step 7. These are short computations with this particular finite vanishing pattern, rather than a new theorem relabelling a clause of the item.

Step 8 uses enough injectives, exact sheafification, and the actual natural cohomology isomorphism of `lem-weil-pbc-exact-functor-complex-cohomology`. The positive cohomology of the original resolution vanishes since r+1 > 0. Assumption (4) applies to J_X H in A'_X from Step 1, and assumption (3) makes A a fine sheaf. Both ends of c_r are therefore fixed by sheafification, so applying exact sheafification and obtaining an isomorphism implies that the original morphism of underlying presheaves is invertible. This is the final substantive argument, not an appeal to a node restating the conclusion. Step 9 merely assembles the specified edges and composition map and writes out the adjoint/counit formula already prescribed in the statement; it uses their stated naturality.

I checked r=0, r=1 (the sole possible obstruction is d2 to R^2 epsilon_* G0), H=0, f the identity whenever it belongs to P, and equal topologies. In equal topologies all positive comparison images are zero and both spectral sequences reduce to the expected identity comparison. No terminal object in the original category, global fibre products, nonzero coefficients, sheaf points, enough points, or additional refinement assumption is used. All cited step dependencies have verbatim quotations in citations.json; quotations for the edge lemma include both edges. No SGA source is used. Every step is under 2000 characters (the longest is 1115), and the elementary steps are explicit universal-property substitutions or spectral-page/filtration calculations after the cited non-elementary theorems have been supplied. The other-unit citations are recorded in split_report.tool_uses as generic tools; they do not replace this unit's geometric route.

## Unfinished work and validation

No mathematical part remains unfinished. The server `review_split` check passed with zero new nodes. The required complete deliver.py dry run and final push are run after writing this report; their terminal outputs provide the delivery outcome.

The first full dry run required the site-localization quotation to be at least 40 characters or the whole statement. I replaced its short formula quotation with the full verbatim statement; the mathematics and node file did not change.
