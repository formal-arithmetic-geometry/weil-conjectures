## Files written

- dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-pullback-stratified-models.json: item, statement, split into eight steps; Mathlib searches found no match.
- citations.json: 18 step/node citations, each checked against the verbatim statement of the existing cited node.
- report.md: this report. No new DAG nodes; no Mathlib leaves added. Sandbox-only bs.txt, write_split.py and searches.jsonl support the work and are not project changes.

## Attachments

None. Searched the live project's WeilConjectures source for the exact blueprint tag, stratified models, finite-projective pullback, and perfect pullback. The sorry-free IsAdicStratifiedLisseSheaf.upperStar and IsFieldStratifiedLisseSheaf.upperStar in SixFunctors/ProEtale/{Adic,FieldCoefficient}/Constructible.lean prove assertions about degree-zero lisse sheaves in different coefficient categories. They do not give this item's unbounded ordinary derived completed-ring statement, its coefficient projection identities or its normalized bounded-projective chart formulas. They are not attachments.

## WANTED

None for this split. The relevant item source and Stacks sources are available locally.

## Corrections and findings

The assigned item was unsplit and there was no earlier sandbox node or report. Its statement is retained verbatim. I read GOAL.md, the three blueprint levels of SETUP.md, the stage-1 contract, the worker role, the chapter and sk-r-real-linear unit records, and delivery-errors B through E. The unit's dual-weight application is served through the existing chain of extractions; this delivery does not replace the unit route or edit its records.

The principal potential C4 error was using lem-weil-pbc-proetale-derived-pullback-composition: its statement requires coefficient identifications, whereas this item supplies coefficient maps. I do not cite it. A contemplated new arbitrary-ringed-topos composition lemma was discarded after the whole-DAG search found lem-sfb-ringed-derived-monoidal-comparisons. Its statement gives precisely the general K-flat-normalized composition and ring-compatible geometric two-isomorphism transport needed here, without flatness or invertibility assumptions. No node was created for that fact. The stronger profinite coefficient inverse-image assertion was also unnecessary and is not used.

Another potential mismatch was an etale/closed-immersion restriction theorem applied to arbitrary covering objects. The proof instead uses lem-weil-proetale-weakly-etale-localization to identify all weakly etale covering slices, identifies their coefficient limits sectionwise, and uses the arbitrary-ringed-site localization theorem. Immersion exactness is used only for i_i and j_i. In particular the derived-complete input hypothesis of the completed-comparison clause of lem-sf-immersion-completed-pullback-comparison is never used to conclude anything about P_fK.

The bounded-flat node lem-pc-bounded-above-flat-kflat-site has a source.place describing 06YS; the local Stacks tags/tags table identifies its actual assertion, lemma-bounded-flat-K-flat in sites-cohomology.tex, as 06YQ. The proof step cites the correct 06YQ label and uses the node's exact, correct statement. I have not changed another worker's node.

## Searches and reuse

I searched all DAG node titles and statements for K-flat pullback, coefficient composition, stratification base change, finite-projective pullback, localized sites, slice restrictions and derived composition. I opened the candidate statements, rather than taking assertions from their proofs. Blueprint searches with tools/blueprint_refs.py included stratification (43 results), ringed topoi (5 results), derived pullback composition (no exact blueprint entry), and pullback/perfect/stratified wording; its ancestor command confirms lem-tw-dual-negation. The current main-20261015 dual-negation proof was read. No other blueprint statement states this entire technical local-model item, so same_as stays empty.

All new Mathlib searches used the prescribed msearch.py Q55/item command and are preserved in searches.jsonl. Both semantic phrasings for ordinary finite-projective pullback and a further phrasing for ringed-topos derived composition were read. Loogle gave ordinary SheafOfModules.pullbackComp, free-sheaf basis formulas, abstract left-derived transformations, and localization comparison infrastructure. LeanFinder/LeanSearch likewise gave underived pullback, scalar extension, condensed modules and general left-derived constructions. The source grep and the actual PullbackFree.lean source show the free-sheaf formulas but not this derived stratified statement. These are not one-line specializations proving all clauses of the item. Existing item search records from its creator were retained, and the actual Q55 searches were appended. No searches were invented or repeated as a substitute for reading earlier results.

## Not duplicates

No new nodes. Finite-free summand flatness and the explicit balanced-tensor/idempotent computation remain elementary proof steps, not additional DAG items. The existing general composition theorem and all geometric and slice tools are cited directly.

## Review by Q55

I read Bhatt--Scholze Proposition 6.6.11 (the definition of locally constant perfect values and its finite stratification) and Remark 6.8.15 (ordinary ringed pullback and naive restriction for etale and closed immersions). They motivate the item but do not spell out all of these canonical maps; the expanded proof is explicitly marked agent-written. I also read the local Stacks statements and proofs of sites-cohomology lemma-derived-pullback-composition (0D6D), lemma-pullback-K-flat (0G7E), the K-flat-resolution/computation discussion (06YS/06YY), sites-modules lemma-localize-morphism-ringed-topoi (04IF), sites lemma-composition-morphisms-sites (03CB), and morphisms lemma-inverse-image-constructible (054I). The new-node source review is vacuous because none were introduced.

Step 1 uses exactly the existing pullback-stratification statement, the constructible-preimage statement, weakly etale base change, fpqc covering base change, and the pro-etale site's specified covering condition. I checked the source scheme of the base change is X_i, not X, and that V_ia is the full scheme fibre product, not a putative factorization based on an inclusion of point sets. Finiteness, disjointness and coverage survive deletion of empty strata. No quasi-compactness or finite-type property of f is inserted.

Step 2 uses the finite-ring status stated by the coefficient-extension node, the explicit formula c_(kh) = c_h h^(-1)(c_k) alpha in lem-trf-constant-coefficient-composition, and the sectionwise inverse-limit universal property. I checked the displayed composite at each finite projection has the same source and target, with alpha suppressed only after specifying it. The projection computation, rather than an assertion that inverse image commutes with inverse limits, proves the completed coefficient composition law. It proves simultaneously the finite-projection compatibility for f j_i = i_i f_i.

Step 3 uses the weakly etale localization node's site equivalence and its identity-on-constant-sections coefficient identification, then the inverse-limit node to identify completed coefficients on slices. The localized-ringed-site node explicitly supplies the localized structural ring map, rather than merely defining localization. Equality with c_v is checked at every finite projection. This handles arbitrary covering objects; they need not be noetherian or immersions.

Step 4 uses the exact general composition and geometric two-isomorphism transport clauses of lem-sfb-ringed-derived-monoidal-comparisons, after step 2 has supplied the ring compatibility. I checked its structural maps are arbitrary maps, and its complexes unbounded. The locally closed immersion node explicitly says ordinary Lu* = u* is exact; I use this only for the two immersions. Completeness and the completed-comparison part of that node are not needed. The direction of the resulting isomorphism is j_i* P_f K to P_fi i_i* K, as required.

Step 5 uses the arbitrary sheaf-slice theorem, whose statement supplies the canonical theta, its K-flat representative normalization, exact restrictions, and the absence of a flatness requirement. In step 3 the slice ringed map was already matched to v_ia; thus theta is being applied to the correct rings, not merely to topoi with similar notation. Inverting theta supplies the displayed direction of the item. Functoriality then carries the GIVEN local model isomorphism into P_v.

Step 6 is elementary: split maps from a finite projective module give split maps from M^q to B_U^r and back. Tensoring with B_U^r is a finite sum of the identity, and kernels/images of a split sum decompose. Consequently the direct summand tensor functor is exact, exactly the definition in def-pc-flat-sheaf-modules. No tensor-exactness assertion about B_U over R is assumed. I did not create a spurious lemma for this few-line argument.

Step 7 uses the bounded-above flat K-flat theorem and the exact computation-counit clause of the ordinary ringed derived pullback theorem. Boundedness is supplied by the given L, and flatness by step 6; neither comes from f. This verifies all of the non-elementary hypotheses required to compute the derived pullback termwise.

Step 8 writes both inverse balanced-tensor maps on the free basis. Their relations use c_v, not an identification of source and target completed rings. The finite constant-section compatibility of the coefficient maps preserves the entries from R; therefore the same matrix idempotent is intertwined on both sides. Matrix representatives between the two chosen free modules then establish commutation with maps of projective summands, in particular all differentials. This supplies a complex isomorphism and exactly the basis/idempotent normalization, rather than only an objectwise isomorphism. The calculation is elementary from the ordinary module pullback definition in the cited inverse-image node and the projection calculation of step 2.

For small cases I checked empty X (all strata discarded), empty individual strata/covers, a chart with rank-zero modules, the zero complex, a one-term free complex, a proper projective summand of a finite free module, and a bounded complex with nonzero differential. The chosen idempotents may vary with the degree; the matrix-between-summands argument does not require a single common idempotent or a splitting of the whole complex. Nonflat abstract coefficient maps are allowed by the same balanced tensor computation and the cited K-flat counit. There is no requirement that P_fK be complete, that c_f be invertible, or that f be separated or linear over a base field. All proof steps have fewer than 2000 characters. I checked C1 and C4 for every step, checked the dependency paths of the generic composition and localization tools do not lead back to this item, and copied/validated each quotation in citations.json from the actual statement used. The off-unit generic tools have individual reasons in split_report.tool_uses.

## Unfinished work

No mathematical part of the split remains. The required server dry run and direct push follow this review; their outcome is reported by the delivery command.
