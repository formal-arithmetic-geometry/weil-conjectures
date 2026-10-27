## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-closed-test-kinjective-section-models.json` (item, statement unchanged, now split); `citations.json` (17 verbatim step citations); this report. `searches.jsonl` contains the actual search-command records, and `write_split.py` is a sandbox-only reproducible writer.

## New nodes

None. No Mathlib leaves created. The six steps use existing nodes rather than extracting the item's clauses into new obligations.

## Attachments

None. The search of `lean/WeilConjectures/` by the exact blueprint tag, K-injective section terminology and closed-test terminology found no project declaration of this item. AffineBasisKInjectiveSectionsPreservesHomology.lean is a Zariski module-section theorem under affine-basis acyclicity, not the condensed pro-etale closed-test statement. The existing parent in `lean/Sheaf/Paper/ClosedTestDerivedExchangeModel.lean` is not an attachment under the required project-root test, and its parent theorem would not replace the representative/unit normalization obligations of this item.

## Literature and searches

WANTED: none.

Read Stacks `derived.tex`, Tag 08BJ, label lemma-adjoint-preserve-K-injectives (statement and adjunction proof), and Tag 015F, label lemma-right-derived-exact-functor (in particular every complex computes the derived functor with its canonical unit). Read `sites-cohomology.tex`, Tag 0D6F, label lemma-unbounded-cohomology-of-open, including the immediately preceding K-injective restriction argument. Read `sites-modules.tex`, Tag 04J0, label lemma-localize-morphism-ringed-sites, including its restricted ring-map formula. Read `proetale.tex`, Tag 09BL, label lemma-closed-immersion-affines-apply, clauses (1)–(2) and their proof. The actual-unit/internal-module enhancement is taken from the existing node lem-sfb-closed-test-unit-evaluation, not claimed to be verbatim in 09BL. Read the current blueprint module-derived-pushpull and right-derived-functor definitions, chapter description, and the current sk-thm-sf-ctf-stability statement/proof. The unit record retains the historical sec-six-functors label; the inherited item chapter/unit and its route are preserved.

The item has no sandbox predecessor to retain. Its inherited five Mathlib searches are preserved. New actual logged searches used LeanFinder, LeanSearch, Loogle, and source grep, with a second semantic phrasing about exact evaluation and normalized derived units. LeanFinder returned generic injective resolutions and SheafOfModules.evaluation/unitHomEquiv, LeanSearch returned injective resolutions and K-injective definitions, and the combined K-injective/section grep and sheaf/rightDerived Loogle pattern returned no hits. Read Mathlib Algebra/Category/ModuleCat/Sheaf.lean at evaluation (85) and unitHomEquiv (178): these define ordinary evaluation and a section/Hom bijection, not closed lifted-test section models, derived comparison units, or slice identifications. The final focused grep was logged too. No new node or unsupported Mathlib match results from these searches.

DAG searches checked the statements of the parent, the four sibling obligations, the actual-unit node, generic K-injective preservation, exact-derived comparison, ringed slice localization, and inverse/direct image definitions. Whole-blueprint searches for K-injective, localization and closed lifted test found no equivalent imported statement. `blueprint_refs.py ancestor` returns None; the inherited null ancestor and via chain are retained, with its exact returned-parent steps 3–4 place and the assembly explained in split_report.blueprint.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to distinguish. The two final exact-derived descent nodes and the generic slice-localization nodes are cited, not recreated.

## Errors and scope

No statement dispute or source correction. No attachment, unproved Lean declaration, or generalized category-theoretic fact was mistaken for the complete item. The imported statement was retained exactly. In particular, the proof does not assume closed pullback preserves K-injectives, does not assume T or T_0 is w-contractible, and does not replace derived object identifications by cohomology-group statements. No SGA route, coefficient change, geometric base-change invertibility, or extra boundedness hypothesis enters.

The off-unit nodes declared as generic tools in split_report.tool_uses are ind-etale base-change stability, normalized exact-derived evaluation, unbounded ringed section localization, coefficient-compatible ringed slice localization, and the two normalized exact-derived descent statements. They provide generic constructions required by this unit's fixed route; they do not replace any geometric step of the unit. The right-adjoint K-injective lemma is already Lean-closed. No top-level tool_uses approval field was written.

## Review by NX

I reviewed this split against B–E with the cited node statements open. There are no new statements to review or unsplit nodes containing hidden proofs. Every non-elementary input is an existing cited node, every step is shorter than 2000 characters (the largest is under 1000), and citations.json records an actual substring of each cited statement. The statement introduces its schemes, coefficients, complexes, resolutions and universe convention. No node is a renamed clause of this item, and nothing cites the parent exchange-model node, so its use of this item creates no cycle.

Step 1 uses lem-sfb-closed-test-unit-evaluation for exactly its internal/ordinary module equivalences, their preservation of quasi-isomorphisms and K-injectivity, their compatibility with adjunctions, exact V-evaluation and the direct-image section formula. I checked that its hypotheses on A, the ideal, the closed lift, and w-contractibility of both V and B are precisely those of the item. It is not the weaker set-sheaf-only 09BL node. This permits ringed-site lemmas with the reconstructed coefficient ring sheaves, without identifying condensed coefficients with discrete coefficients.

Step 2 uses the adjunction clause of sk-def-sfb-module-pushforward-pullback and 08BJ as stated by lem-weil-pbc-right-adjoint-preserves-kinjective. The latter allows any K-injective complex; it requires no injective-term or bounded-complex hypothesis. The exact-left-adjoint hypothesis is already an assumption of this item. The actual computation of Rf_* is supplied by sk-def-sfb-module-derived-pushpull, and the inverse resolution comparisons use def-sfb-right-derived-functor's invertible unit at K-injectives. The quasi-isomorphism j and exact h^* give J the required representative of h^*K.

Step 3 cites both exact evaluation from the actual-unit node and the theorem lem-weil-pbc-exact-functor-derived-functor. I opened the latter and checked its assertion is about the canonical right-derived unit on every complex, not just an arbitrary isomorphism RF≅D(F). Thus the comparison applies to C=s^*f_*I even if C is not K-injective. Evaluation followed by forgetting the section-ring module action is exact; the forgetful functor preserves kernels and cokernels by the elementary definitions of modules and abelian groups. Applying s^* to the resolution comparison is valid because it is exact. The arrows are inverse universal units after these comparisons, as the item requires.

Step 4 is elementary assembly from the actual-unit node. I checked the inverse direction: the node's u goes I(T)→(s^*f_*I)(V), so the displayed first-line arrow uses u^{-1}. Naturality at the differential gives the written square u^{n+1}d^n=d^nu^n, proving it is an isomorphism of complexes. The direct-image section formula identifies J(X_Z×_Z V) with J(T_0) by the specified fiber-product projections. No new theorem is hidden in this step.

Step 5 uses lem-sfb-unbounded-sections-localization, whose statement explicitly gives a derived-category isomorphism represented by the degreewise identity for any K-injective representative. It is not merely the cohomology-group statement in Stacks. I checked its small ringed-site, coefficient, and universe hypotheses through step 1 and the item's common-universe convention. I initially cited the pro-etale site definition alone for validity of the two test objects; on re-reading it, that definition did not assert base-change stability. I repaired this by citing lem-weil-pbc-ind-etale-stability, whose statement supplies base change and ind-etale implies weakly etale. The full site definition then says these maps are objects. The slice comparison is applied on X and X_Z, respectively, with I and J, so it never assumes the complexes or schemes coincide. No w-contractibility of these source objects is used.

Step 6 uses lem-weil-pbc-localize-ringed-site-morphism for its actual coefficient-compatible inverse-image square and restricted ring map, and def-pur-localized-ringed-site for sectionwise restriction. Substitution V=T and U=h^{-1}T=T_0 is justified by the two fiber-product universal properties: both T_0=X×_U V and X_Z×_X T map to X and V compatibly, giving inverse projection-preserving maps. The induced localized morphism is the closed pullback a. I checked the direction j_{T_0}^*h^*≅a^*j_T^* by taking the inverse of the node's pullback comparison if needed. The two exact-derived nodes specify both composition and natural-isomorphism descent at complexes, so the last comparison retains its localization normalization instead of choosing an isomorphism arbitrarily.

Small cases: for the zero ideal, s and a are identities and the actual-unit and localization comparisons specialize to their identity normalizations. For the unit ideal, V and T_0 are empty; the assumed unit-evaluation isomorphism still applies (the lift is governed by its stated hypotheses), and the empty-site section groups are zero. For A=0, empty X, or the zero coefficient ring, the respective section complexes are zero and all displayed isomorphisms persist. No nonzero-ring, nonempty-test, Noetherian, torsion or flat-scalar hypothesis was introduced. K may have any lower cohomological bound and the chosen K-injective I,J may be unbounded; 08BJ, 015F and 0D6F apply to those complexes directly.

No second worker was started: this is the direct-delivery self-review authorized in the brief. Nothing remains mathematically unfinished in this one-level split; its existing unsplit dependencies remain their own work items.

## Validation

The initial server review_split check passed with zero new nodes; its note is that the inherited unit has no realization recorded yet. The delivery dry run completed successfully: OK (not pushed), preflight passed, temporary head aabc96f900d. No process remained active after that result. This report update is followed by the final dry run and direct push required by the brief.
