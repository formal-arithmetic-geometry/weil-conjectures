## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-site-fp-stalk-realization.json`: item, statement unchanged, split into five proof steps; not a Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-left-exact-left-adjoint-slices.json`: statement-only Mathlib leaf, one general categorical fact used to build the point on the slice.
- `citations.json`: verbatim statements for every proof-step citation.
- `searches.jsonl`: actual search-command log; original item searches are retained in the item, and the present searches are added rather than replacing them.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag, by stalk-realization spellings, and by finite-presentation/stalk/matrix notions found no declaration stating the item. The existing Point/Flat, Point/Linear and sheaf Quasicoherent extensions give other assertions, not this realization. Upstream master is not used as evidence of a proof.

## Wanted sources

None. All sources used are available locally.

## Audit findings and corrections

The item was unsplit and had no proof. Its statement agrees with the local-realization argument in Stacks `sites-cohomology.tex`, Tag 0DEN, label `lemma-check-K-flat-stalks`, proof of (1). Its extra explicit clauses about the localized point are supplied by `sites.tex`, Tag 04H2, label `lemma-point-localize`, and the slice construction in Tag 04H1, label `lemma-localize-morphism-topoi`. No hypotheses or conclusions were changed.

An important citation distinction is that `lem-trf-site-point-fibre` states the module-colimit assertion only for a constant coefficient ring. Our ring sheaf R is arbitrary. I instead use the statement of `lem-trf-site-point-reconstruction-sets`, which covers every sheaf of sets and expressly gives the small cofiltered pointed-object category and the canonical section-to-germ map. Lifting the finite matrix requires only this set-level result and a finite common refinement; it does not require an uncited theorem about variable-ring colimits or descent categories of finitely presented modules.

The new node is not a renamed clause of the item: it is an assertion about an arbitrary left exact left adjoint between categories and its arrowwise functor on slices. It contains no site point, ring, matrix, or finitely presented module. Both its conclusions are already in Mathlib. The point q is constructed in the item's own step 3; the comparison on restriction and the effect on the coefficient sections are proved in step 4; the actual module sheaf is constructed in step 5.

The new leaf was searched throughout the DAG by its concept and by `Over.post`, `postAdjunctionLeft`, `isLeftAdjoint_post`, `overPost` and Tag 04H1, throughout the blueprint using `tools/blueprint_refs.py search` for slices, over categories, left exact left adjoints and 04H1, and in the project Lean source. No existing node states it. Mathlib's two relevant instances were then read in their pinned source files: `CategoryTheory.Over.isLeftAdjoint_post`, `Mathlib/CategoryTheory/Comma/Over/Pullback.lean:138`, and `CategoryTheory.Limits.PreservesFiniteLimits.overPost`, `Mathlib/CategoryTheory/Limits/Preserves/Shapes/Over.lean:48`. The explicit adjunction preceding the former at line 133 confirms that the source category must have pullbacks, which follows from the finite-limit hypothesis in our leaf. The definition `Over.post` agrees exactly with our arrowwise functor.

The initial exploratory grep under `CategoryTheory/Topos` returned no hits; that directory search is not used as evidence of absence. The subsequent searches across `CategoryTheory` located and verified the actual declarations. Search results for `SheafOfModules.IsFinitePresentation` and `QuasicoherentData.IsFinitePresentation` were read in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`: they concern presentations of already existing sheaves, not realizing an arbitrary module over a stalk. Two semantic phrasings of the item and two of the categorical fact were tried. No unavailable service has been recorded as a failed match.

## Not duplicates

lem-sfb-left-exact-left-adjoint-slices vs lem-weil-pbc-slice-site-localization: the latter starts with a continuous site functor defining a site morphism and describes localization and comparisons on localized sites; our leaf starts with any categorical left exact left adjoint and states preservation of finite limits and existence of a right adjoint for the arrowwise slice functor.

lem-sfb-left-exact-left-adjoint-slices vs lem-weil-pbc-localized-sheaves-over-representable: the latter identifies sheaves on C/U with sheaves over a sheafified representable; our leaf concerns adjoints on abstract slice categories. The existing equivalence is cited separately.

No existing node carries the new leaf's source tag 04H1. The blueprint searches found no equivalent blueprint node, so `same_as` remains empty.

## Review by Q21

I read the source paragraph of Tag 0DEN and its reference to the finite-presentation descent result, and checked our replacement finite-coefficient argument against it. The source only needs a finite matrix to descend. Our argument uses exactly that finiteness, and the module sheaf is the cokernel of the descended matrix rather than data selected by an unspecified existence assertion. I also read Tag 04H2 and the full statement of Tag 04H1. They justify treating a point as a geometric morphism and passing to a slice without assuming the site is subcanonical. The new leaf's categorical statement was checked against both Mathlib instances, not inferred from its title.

Step 1 uses the statement of `lem-trf-site-point-reconstruction-sets`: it explicitly has arbitrary sheaves of sets, canonical germs, smallness and cofilteredness. Its hypotheses are precisely the present small site with finite limits and our geometric morphism p. In step 2, `def-sc-finitely-presented-module` supplies the finite free presentation. Taking standard-basis coefficients, representing each coefficient, and restricting to a common predecessor are finite elementary operations using the cofiltered category from step 1. The cited geometric-morphism definition supplies product preservation, so addition and multiplication of sections give the ring germ map rather than an unrelated set bijection.

For step 3 I opened `lem-weil-pbc-localized-sheaves-over-representable` and checked that its equivalence is for arbitrary sites and sheafified representables. I opened `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` to supply finite limits in the sheaf category before applying the new slice-adjoint leaf. The latter gives exactly both properties of the arrowwise functor P that the step uses. The remaining fibre-at-x functor has its right adjoint written explicitly; there is no appeal to an unnamed theorem saying that site points localize. Its singleton fibres away from x ensure maps over S are completely determined by a map from the x-fibre. Composing adjoints and finite-limit-preserving functors is the defining Hom-set calculation for the composite, as used in `def-trf-geometric-morphism`.

For step 4 the cited slice-equivalence statement includes the explicit quasi-inverse fibre formula. Applying that formula to G times H proves its identification with restriction, using `def-pur-localized-ringed-site` for sectionwise restriction. Taking p-inverse image and then the fibre at x gives the displayed natural comparison. I checked the operations as actual maps on finite products: this verifies ring and module compatibility. The graph of a section r is sent to its value at x, so the R(U)-to-R_p map here is the same germ map that lifted the matrix in step 2. This comparison is a short direct evaluation, not an unexplained transport assertion.

For step 5 the module-sheaf definition states that the category is abelian and cokernels are sheafifications of sectionwise cokernels. The formula for alpha is compatible with restrictions because these preserve addition and multiplication. I opened `lem-trf-geometric-inverse-image-exact`, whose statement explicitly covers arbitrary commutative ring sheaves and cokernels with transported scalars. Apply it to q with ring R_U; step 4 supplies q-inverse R_U = R_p, so no flatness or change-of-scalars hypothesis is missing. Finite powers use only finite products, and the image matrix is calculated coordinatewise. The resulting cokernel is M by the chosen exact presentation.

I tested M=0, a=0 (a finite free stalk module), b=0, the empty coefficient matrix, and the zero stalk ring. With no matrix entries, nonemptiness of the cofiltered pointed-object category still supplies U and x. Nothing assumes a nonzero ring, positive presentation ranks, a local stalk ring, enough points, or a subcanonical topology. For the new leaf, L equal to the identity and X terminal reduce to the original adjunction, and the empty-category case is excluded already by existence of finite limits; the Mathlib hypothesis HasPullbacks is present through finite limits. All five steps are shorter than 2000 characters. The split stays within the local algebra used in the existing K-flat stalk criterion and introduces no SGA source. Three off-unit uses are declared as generic tools, with the reason for each in split_report.tool_uses.

No statement dispute was found, and no work remains mathematically unfinished. Server diagnostics and the final dry run are recorded below.

## Validation

Server `review_split` passed and server `check_dag` reported no finding introduced by the sandbox or its nodes. The full required `deliver.py --no-push` exited successfully: `OK (not pushed)` at commit `541a49d61d`, with preflight passed. The report is finalized with these results before the final dry run and push. No Lean file was written and no compiler, Lake command, local DAG check, git command, or source-tree mutation was performed by this worker.
