# NK: lem-trf-big-small-etale-pullback-formula

## Files written

- dag/nodes/sec-trace-formula/lem-trf-big-small-etale-pullback-formula.json — statement, split into eight proof steps; statement and inherited metadata retained. Mathlib has generic restriction/adjunction tools, but no exact match for this small/big etale comparison.
- citations.json — verbatim statement witnesses for all 21 step/node citations.
- report.md — this report and signed self-review.

There are zero new nodes and zero new Mathlib leaves. searches.jsonl contains the actual search-command output; write_split.py is a sandbox-only preparation script, not a delivery file.

## Attachments

None. Read-only searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures and Comparator for the exact blueprint tag, bigEtale/big_etale/BigEtale, and the small/big etale notions found no declaration stating the item. The mentions in AlgebraicGeometry/Sites/Gm.lean concern the global-functions sheaf and do not prove this statement for every abelian sheaf. The small-etale upperStar/lowerStar declarations do not supply the big-site comparison. No master sorry declaration was treated as a proof.

## WANTED

None: all sources used are present locally.

## Findings and changes

The item had a correct statement and no proof. Its evaluation assertion is the first assertion of Stacks 09XN (etale-cohomology.tex, lemma-describe-pullback); the final comparison is Topologies 021I(3), lemma-morphism-big-small-etale. I retained every hypothesis and both naturality clauses. The fpqc-sheaf assertion also present in 09XN is not asserted by this item.

The proof does not assume that extension to the big site is an equivalence, or that a general big sheaf is pulled back from the small site. It constructs the big restriction/product adjunction, computes the direct-image square, and uses the existing adjunction-conjugacy leaf. It then evaluates using the exact-retraction unit and checks restriction maps with that same unit-normalized comparison. There is no new node restating an item clause. The product/graph Hom bijections are written out instead of introducing a new localization lemma: they use only fibre-product identities and the existing natural-bijection adjunction leaf.

I corrected an initial source-label typo in the sandbox: the localization definition is Sites Tag 00Y0, not 00X0. No mathematical statement was corrected; there is no statement dispute. No dependency of the imported statement was removed, and no unit or chapter binding was changed.

## Searches and duplicate audit

I read the item, the exact-retraction node, all cited node statements, and the relevant generic site-localization and adjunction nodes. Whole-DAG searches used 09XN, 021I, 021H, 03CE, lemma-morphism-big-etale, localization/right-adjoint terminology and small/big etale terminology. Blueprint searches were run for big small etale, 09XN, slice site, localization direct image, localize-given-products, 03CE, localization product and pullback sections. No blueprint node states this item. blueprint.same_as remains []. The ancestor query returns lem-trf-local-term-locality, and the inherited from.place/via are retained.

Mathlib searches were run only through the required msearch.py command. Their original results are in searches.jsonl and were copied verbatim into mathlib_searches, in addition to preserving the imported evidence. Both localization/product and etale-specific questions were tried with alternative natural-language phrasings, Loogle and grep. The hits in Sites/Over.lean give overPullback, overMapPullback and continuity of Over.star/Over.pullback. CoverLifting and Pullback give generic sheaf adjunctions; Adjunction/Restrict.lean and Whiskering.lean explain generic adjunction restriction. None states the etale small-to-big evaluation formula. I read the source of these candidates; the requisite categorical tools already have DAG nodes. No invented searches and no unavailable service recorded as absence.

## Not duplicates

No new nodes are created. In particular the existing localization definition, fully-faithful adjunction restriction leaf, natural-Hom-bijection adjunction leaf, small-etale inverse-image composition lemma and conjugate-iso unit-equation leaf suffice; no duplicate product-localization or comparison node is delivered.

## Review by NK

I read Stacks 09XN, lemma-describe-pullback, including its first proof paragraph, and Topologies 021F, 021G, 021H, 021I and 021J in topologies.tex. I also read the localization construction and restriction formula at Sites 00Y0 and the full statement and proof of 03CE, lemma-localize-given-products. The categorical sources read are Categories 0037, definition-adjoint and its following unit/counit discussion, and 0B65, lemma-transformation-between-functors-and-adjoints. The actual tag-to-label mapping was checked in tags/tags. For the unit route I read dag/chapters/sec-trace-formula.json, dag/units/sk-i-curve-zero.json, and the current main-20261015 proof of lem-trf-local-term-locality. This item is a tool below its normal-cone/ph-etale descent input, not the unit's key node. No unit realization fields are changed.

Step 1 uses def-weil-size-convention for compatible small presentations, def-pur-localized-ringed-site for the actual restriction formula and induced coverings, def-pc-fibre-product for the scheme products, and def-weil-pbc-sites-and-cohomology(1) for base change of a covering. I checked that the covering pullback is along W times_Y X -> W in B_Y; W need not be etale over Y. This avoids applying a small-site lemma with an absent etaleness hypothesis. Identifying B_X with the slice and rewriting the sheaf equalizer are elementary from those statements.

Step 2 uses def-pc-fibre-product for both graphs and the projection identities, and lem-weil-pbc-adjunction-of-natural-bijection for turning the explicitly inverse natural Hom maps into an adjunction with the specified unit. That leaf states the unit formula used here. I checked both composites: p composed with the graph is the identity, and v(p) composed with the graph at v(W) is the identity. Thus the big unit is the actual restriction along the projection, including for a non-monomorphism X -> Y. This is a direct construction, not an appeal to a missing big-etale theorem or a definition used as a theorem.

Step 3 uses precisely the restriction formula in lem-trf-big-small-etale-exact-retraction and the underived formula (u_*F)(W)=F(W times_V U) in def-weil-pbc-direct-image. I checked the statement of each; their derived claims play no role. Both composites evaluate at the very same X-object W times_Y X, on maps as well as objects. No properness or finite-type assumption is introduced.

Step 4 uses the composite-unit formula of def-weil-pbc-composite-adjunction, the abelian inverse/direct-image adjunction of def-weil-pbc-sites-and-cohomology(3), and existence, invertibility and uniqueness with the unit equation from lem-weil-pbc-conjugate-iso-unit-equation. The right-adjoint comparison is oriented f_s,* R_X -> R_Y Q_f, so its conjugate has the required orientation P_f L_Y -> L_X f_s^-1. The displayed equation (*) is the exact unit equation, not a free choice of isomorphism.

Step 5 uses lem-weil-pbc-inverse-image-composition(1),(2), including its displayed unit equation, def-weil-pbc-composite-adjunction for the two units, def-pc-fibre-product for the iterated-product comparison, and uniqueness from lem-weil-pbc-conjugate-iso-unit-equation. I checked the direction of c carefully: h_s^-1 a_s^-1 -> (ah)_s^-1. Substitution of (*) gives the same comparison on the two right adjoints because their projections to W and T' agree. This proves (**), rather than assuming a coherence isomorphism without a normalization. The small-etale composition node is the one generic off-unit tool declared in split_report.tool_uses; no trace-unit step is replaced.

Step 6 uses the isomorphism of the canonical unit from lem-trf-big-small-etale-exact-retraction, and def-weil-pbc-sites-and-cohomology(2) for evaluation/global sections. In particular the unit inverted is for the sheafified inverse image, not for a presheaf Kan extension. Evaluation at T/T now gives the claimed abelian-group isomorphism. All maps used are abelian-sheaf maps, which checks the coefficient category rather than silently changing from sets.

Step 7 uses def-pc-fibre-product, the adjunction conventions of def-weil-pbc-sites-and-cohomology(3) and the underived direct-image formula of def-weil-pbc-direct-image. Evaluating (*) at the final object gives (***); the big unit from step 2 becomes restriction along h and the small unit becomes pullback of global sections. It does not cite a finite-morphism section-pullback definition for arbitrary h.

Step 8 is substitution of the previous equations and naturality of beta_a and e_T', using only the actual composition isomorphism stated by lem-weil-pbc-inverse-image-composition. The equality displayed there proves the restriction clause for arbitrary T' -> T over S. No hidden compatibility with sections is left to an unspecified transport.

For delivery-errors B--E I checked that every non-elementary assertion above is either constructed in the step or supplied by the cited statement, with a literal quote in citations.json. There are no new statement-only nodes to audit for B1/B2, no new definitions or duplicate clauses, no new Mathlib claims, no forbidden SGA source, and no cyclic proof through an item descendant. Every proof step is shorter than 2000 characters; the Hom-bijection and coherence steps each carry one routine argument, not an omitted auxiliary lemma. I checked the mathematical edge cases: f=id (product with the terminal object and the identity adjunction); F=0 (all maps are zero-object isomorphisms); T or X empty (the empty cover forces a zero group of sections); and a non-etale h such as a closed immersion (allowed since h is used only in the big slice and in the small base-change functor). Nothing uses connectedness, a geometric point, torsion, quasi-compactness or properness. No unresolved mathematics remains.

## Unfinished work

None. Required remote dry run and delivery results are recorded below when they complete.

## Validation

The remote review_split check passed with zero new nodes. The first full dry run rejected two formula-only citation excerpts as shorter than its 40-character minimum; I replaced them with the complete underived direct-image definition, including its action on restriction maps. No proof or statement changed.
