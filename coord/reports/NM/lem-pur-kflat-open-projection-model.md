# Worker report: lem-pur-kflat-open-projection-model

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-kflat-open-projection-model.json: statement, split; six proof steps, all using existing nodes. No statement or statement-dependency changes. Mathlib verdict: no exact match or one-line specialization.
- citations.json: verbatim cited statements indexed by proof step.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. The sandbox initially contained only dispatcher marker files. There was no interrupted split, report or delivery invocation to resume. prepare.py is a sandbox-only preparation script; searches.jsonl is the search command's unmodified log.

## Attachments

None. I searched the whole project WeilConjectures tree for the blueprint tag and K-flat/projection notions. The tag is absent. The generic module-object projection formula concerns a different adjunction, and the pro-etale finite-coefficient scalar projection theorem does not state this small-etale open chain-map computation with the specified comparisons. They are not attachments. No Lean was written or compiled.

## WANTED

None. The Stacks source needed is present.

## Audit of the imported item and route

I read GOAL.md, the stage-1 brief, stages/1-dag.md, the worker role, the human's three blueprint levels in SETUP.md and both copies of delivery-errors.md B–E. I read the chapter and unit records, the current main-20261015 purity-transport unit and thm-pur-rational-and-qbar-purity proof. This is a finite-coefficient prerequisite of the Locality comparison, not a substitute route for smooth purity. No SGA source is used.

The item was unsplit, without a released repair order. Its parent has already extracted this assertion as one of the genuinely distinct ingredients of the support comparison. I retain the statement and imported provenance verbatim. The source phrase about the report belongs to the creating worker's provenance; the actual argument is now in the node's steps. blueprint_refs.py ancestor prints a null ancestor, as already recorded on the item; I retain that value and its via chain rather than inventing a blueprint ancestor. The from.place is already specified. Whole-blueprint searches for projection, K-flat and 0FPI found no statement equal to this one; same_as remains empty.

## Mathlib searches and readings

The five searches in searches.jsonl were executed through the required msearch.py command and their results read. Both semantic phrasings were tried. Loogle returned no hits. Grep returned only totalLeftDerivedCounit and its use, at Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean:198,203,205; I read that source. LeanSearch returned generic Adjunction.derivedε and derivedη and projective-resolution naturality lemmas; I read Derived/Adjunction.lean. LeanFinder returned ordinary module scalar extension, sheaf pushforward adjunctions and Tor functoriality. These do not compute this specific mixed K-flat tensor model, do not have the open direct-image comparison, and do not identify its normalized scalar mate. The item's previous searches are retained and the new searches appended with their actual hits. No unsuccessful service response was recorded as absence.

## Not duplicates

No new node is created, so there is no new/existing pair requiring a distinction. Existing generic tools are cited instead of creating a mixed tensor lemma, a derived transpose lemma or a scalar-mate lemma. I also read lem-sp-flat-coefficient-chain-transpose, which assumes that both complexes in its scalar computation are K-flat; it cannot be applied directly to C=j_*j^*I here. The proof uses the arbitrary-complex chain-transpose lemma and fixed-factor K-flat tensor lemma instead.

## Review by NM

I read Stacks sites-cohomology.tex Tag 0FPI, label lemma-adjoints-push-pull-compatibility, including its proof through K-injective/K-flat representatives. Its assertion is a canonical counit square, not a projection-formula isomorphism theorem. I read Tag 07A4, label lemma-pullback-tensor-product, including its representative construction, and checked the tag/label mapping in tags/tags. The resulting specialized argument is marked agent-written; the Stacks sources motivate and normalize it rather than being silently treated as a theorem stating this entire item. I read Tag 06YS, label lemma-K-flat-resolution, through the existing resolution node and its source context. No new statement-only nodes need sources.

Step 1 uses the exact statements of lem-weil-pbc-kflat-fixed-tensor-triangulated (fixed flat-term K-flat tensor is natural and works on arbitrary complexes), lem-pc-kflat-resolution (a flat-term K-flat resolution of every complex), lem-pur-derived-change-of-rings (scalar extension computed on such a resolution), and lem-pur-change-of-rings-tensor-comparison (ordinary restricted extension is the tensor). The two arrows from Q tensor R are quasi-isomorphisms for different reasons: Q is K-flat for R to X, whereas R is K-flat for Q to B. This prevents the false assumption that tensoring any complex with Q to B is a quasi-isomorphism. The scalar identification is checked on their common model.

Step 2 uses the exact pullback-preserves-K-flat statement, ordinary cochain comparison with naturality and signed symmetry, the canonical derived tensor/pullback theorem and representative-descent statement, in addition to the resolution/fixed-tensor lemmas. I checked that the first applies to a morphism of ringed topoi, as supplied by the small etale inverse image, and has no flatness assumption on a coefficient ring map. Only the flat-term K-flat Q and the chosen R are fed to this lemma. C and I are not declared K-flat. Cancellation after R to X gives the mixed representative square. This step is a concrete two-square normalization argument, not an unstated theorem that all arbitrary tensor models compute derived tensor.

Step 3 cites lem-sp-etale-derived-chain-transpose, whose statement explicitly includes both the formula for an arbitrary chain map and the special case giving the counit square. I checked that its domain is arbitrary complexes and that its canonical alpha is exactly the comparison assumed in the item. It needs neither acyclic direct image nor preservation of injectives.

Step 4 uses the same three existing statements for natural tensor computation, ordinary tensor/pullback coherence and the counit square, with Steps 1–3 already established. The displayed cancellation is j*ell(a) followed by its inverse, valid because a is a quasi-isomorphism and inverse image is exact. It leaves the explicitly displayed three-factor expression. Moving the coefficient factor second uses the signed symmetry already supplied by the ordinary cochain comparison, so it introduces no untracked sign. This also fixes the target identification to e_N ell(a)^{-1}.

Step 5 cites the actual definition of the canonical projection-formula morphism and the actual Hom-bijection statement of the chain-transpose lemma. They state exactly the counit/tensor composite and bijection used here. Equality of the explicit transposes proves equality of the specified maps; it is not merely the existence of some isomorphism between their sources and targets.

Step 6 uses lem-pur-etale-scalar-mate-projection, lem-sbc-canonical-restrict-scalars-functor-comparisons and prop-weil-pbc-inverse-image-modules-exact. I checked the scalar-mate theorem's three bounded-below assumptions for its object j*L, its scalar extension and T Rj_*j*L. Exact pullback preserves the two needed lower bounds, and the remaining bound is stated in the item. The B-direct-image lower bound is also explicit. The restriction/direct-image theorem asserts a canonical bounded-below comparison, not preservation of injectives; that stronger and generally false assertion is never used. Naturality follows from the natural comparisons and adjunction bijection already cited.

For C1 and C4, every substantive ingredient above is an existing cited statement, read in full, and citations.json copies those statements verbatim. For B, there are no new nodes, hollow definitions, invented declarations or unlogged searches. For D, the item contains the actual chain-level cancellation and representative calculation; no node restates a clause. For E, I tested identity open immersion (counits become identities and the replacement cancels), empty open (zero source and target), A=B (the normalized coefficient projection is identity), zero L and zero B, and nonflat A to B (for example Z/4 to Z/2). None requires coefficient flatness: the chosen Q supplies it in the derived calculation. The proof asserts no projection-formula invertibility in general. All six steps are below 2000 characters and conceal no separate unresolved comparison lemma. I checked all cited dependency closures: none reaches this item. Off-unit citations are declared as generic tool uses in split_report, with their purpose, and preserve the purity-transport route.

## Incomplete work

None in this one-level split. Existing unsplit dependencies remain their own items. Final server dry-run and push results are recorded below after the required commands finish.
