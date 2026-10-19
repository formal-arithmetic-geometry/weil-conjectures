# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-dg-etale-injective-finite-cech-rows.json`: item split; no new nodes.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. I searched the project source for the item id and its finite Cech/injective terms; no sorry-free project declaration states the full item.

## WANTED

None.

## What I checked and changed

The item source is the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-dg-finite-type-constructibility.proof.md`, paragraph 2, with the imported statement's source pointing to the finite Cech corollary of Stacks Tags 08FI, 0136, 0137 and 02FU. I read the Stacks proof of `lemma-covering-resolution` in `cohomology.tex` and the localized module-site construction and exactness in `sites-modules.tex`. I also read the existing DAG statements for `lem-weil-pbc-etale-site-localization-open`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-sp-right-adjoint-preserves-injectives`, `def-weil-pbc-inverse-image`, `lem-weil-pbc-product-injectives`, `def-weil-sheaf-of-modules-category`, `def-weil-pbc-direct-image`, `lem-weil-pbc-ses-injective-kernel-splits`, and `def-sp-injective-resolutions`; every citation in `citations.json` is copied verbatim from the corresponding statement.

Step 1 checks both hypotheses needed for restriction of an injective module sheaf: the etale localized-site equivalence identifies module categories, and the existing exact extension-by-zero adjunction gives injectivity preservation. The inverse-image/direct-image adjunction then gives injectivity of each open direct image. I explicitly checked the empty open, where the module category is zero.

Step 2 checks that finite products/direct sums of the open direct images are injective using the existing product-injectives node, that the displayed maps are module morphisms, and that the alternating differential squares to zero by pairwise sign cancellation. The direct-image statement supplies the section formula used here. On resumption I corrected a citation overreach: the module-sheaf definition states the module structure and linearity of morphisms, but not sectionwise products. Step 2 now proves sectionwise products by coordinatewise gluing and the finite coproduct property by summing the coordinate inclusions; its definition quote now supports exactly the linearity it uses.

Step 3 is the signed insertion contraction. For an etale test object factoring through a member of the cover, I wrote the insertion map with the exact sign depending on the number of indices below the fixed member and checked both cases (the fixed index present or absent). The computation gives `dh+hd=1`, including the augmentation degree and the top degree.

Step 4 passes from the contraction on each covering open to exactness of sheaves by the sectionwise kernel/cokernel description. It separately checks the augmentation kernel and the allowed empty-cover case (`r=0` forces `X=∅`, hence `J=0`).

Step 5 forms the cycle short exact sequences. Starting with `Z^0=J`, each term is injective by step 2. The existing injective-kernel splitting statement supplies retractions. The next cycle is a retract of the injective term; I wrote the extension argument proving it is injective, so the induction supplies all cycle injectivities and all required split short exact rows, including `r=1` and the terminal zero cycle.

I searched the whole DAG and blueprint for Cech, injective-row, localized-site, and exact-stalk results before adding anything; the DAG already contains the necessary smaller statements, so no new node was created. I ran the required searches for the item with `msearch.py` (LeanSearch, LeanFinder, Loogle, and Mathlib grep), read every hit, and recorded the exact queries/results in the item's `mathlib_searches`; Mathlib has generic Cech constructions and generic injective splitting but no theorem for this finite ordered etale module-sheaf row.

## Review by Q68

I reviewed the item against the statement clause by clause: arbitrary scheme and commutative ring, finite ordered open cover with the stated empty-cover convention, constant-ring module sheaves, restrictions/direct images, alternating strictly increasing finite rows, injective terms, split exactness, and the `r=0` interpretation. The proof uses only existing DAG statements whose full text I opened; the `citations.json` quotes verify that each cited statement says the fact used. The only generic cross-unit inputs are the localized-site/module adjunction and the localized etale-site equivalence, recorded in `split_report.tool_uses` with why this unit needs them. I tested the edge cases of an empty cover, a singleton cover, and an empty intersection: the zero terms and augmentation behave as claimed. I also checked that all steps are below the long-step threshold and that `proof_deps` is exactly the union of the step uses.
