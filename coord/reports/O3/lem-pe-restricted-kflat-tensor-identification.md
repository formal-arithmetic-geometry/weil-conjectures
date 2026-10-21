# Stage-1 delivery: lem-pe-restricted-kflat-tensor-identification

## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-restricted-kflat-tensor-identification.json: statement node, split in seven steps; no full Mathlib match. The original statement and its seven statement dependencies are unchanged.
- citations.json: twelve entries, covering every cited node at every proof step, with verbatim quotations checked against the current repository statements.
- report.md and searches.jsonl: report and the six new actual search-command records.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this item is a subsidiary comparison, not the integral criterion's key node.

## Attachments

None. Searching the item's blueprint tag in lean/WeilConjectures returned no declaration. The relevant RestrictScalars, ChangeOfRingsAdjunction, ChangeOfRingsTensorComparison and finite-coefficient FlatModel files give individual ingredients, a topological-space comparison, or bounded constant-coefficient cases. None states every clause here for a general site, unbounded K-flat resolution and an arbitrary intermediate-ring-linear coefficient map. In particular partial project declarations and Mathlib components have not been called attachments.

## WANTED

None. All mathematical sources used were available locally. The inherited brief's coord/dag-sync.md is absent in this live read clone; the current direct-delivery instructions and main-20261015 blueprint were followed.

## Audit and corrections

The imported item was statement-only. Its statement is consistent with the source refinement and needs no dispute or correction. I supplied the proof rather than introducing a lemma for its individual clauses. The only non-elementary inputs are the existing generic exact-restriction theorem and derived change-of-rings computation. The remaining maps are constructed by tensor balancing, sheafification uniqueness, localization's defining property, and composition of isomorphisms.

I read the chapter, integral-criterion unit, blueprint ancestor and its second proof paragraph. This item serves the identification of the successive coefficient tensor complexes while retaining their intermediate quotient-ring actions. It does not change the chapter or unit route. The generic ordinary coefficient adjunction and derived change-of-rings statements are declared as tool uses in split_report.tool_uses: the unit does not itself prove these generic constructions.

Whole-blueprint searches for K-flat tensor model, scalar-first and termwise restriction found no equivalent full statement; the two termwise restriction blueprint hits concern internal ring objects and derived adjunctions, not this coefficient-map formula. DAG searches by scalar restriction, exactness, tensor/K-flat terminology and relevant tags located the existing ingredients, so no new node was necessary. blueprint.from.place already names the exact second-paragraph identification; its ancestor and via are retained and same_as is the searched empty list.

The Mathlib searches were actually run with the required msearch.py command. All six searches succeeded, with two distinct semantic phrasings. Loogle and LeanSearch returned ordinary restriction declarations; the first LeanFinder returned module extension-adjunction formulas and presheaf tensor maps, and the second returned exact-derived-functor, Ext and sheaf-symmetry components. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean:36-43, Presheaf/Monoidal.lean:45-103 and Algebra/Homology/DerivedCategory/ExactFunctor.lean:36-105. These are ingredients, not a full match. The historical searches already present in the repository item were retained with their original records; the six new entries copy the exact tool/query fields from this sandbox's search log.

## Not duplicates

No new nodes were created. Existing nodes supply all non-elementary facts; there are no new/existing tag pairs to justify.

## Review by O3

I read the item against sites-cohomology.tex Tag 06YY (lemma-derived-base-change) and Tag 06YT (lemma-derived-tor-quasi-isomorphism-other-side). The identity underlying topos gives change of ring sheaves, without any flatness of the ring map. I also read sites-modules.tex Tag 03EK (section-tensor-product), Tag 03CY (lemma-sheafification-presheaf-modules), and the kernel/cokernel construction surrounding Tag 03DA (lemma-abelian). These justify the explicitly written tensor/sheafification route. The refinements concerning an arbitrary A-linear h and the final conjugation are agent calculations, so proof_origin is agent, not a claim that Stacks explicitly states this entire refinement. There are no new-node sources to review.

Step 1 cites lem-pur-sheaf-ring-coefficient-ordinary-adjunction for the precise assertion that restriction preserves finite limits and finite colimits, def-pc-sheaf-restrict-scalars for additivity, and def-weil-abstract-derived-category for cohomology as kernel modulo image. I opened each statement: the first really supplies both exactness directions on a general ringed site with independent universes. The site's stipulated smallness supplies its module/sheafification hypotheses. It follows that cohomology commutes with restriction and quasi-isomorphisms are preserved, without assuming restriction preserves K-flatness.

Step 2 cites the derived-category definition, which really defines localization at quasi-isomorphisms and the shift with differential -d, and the scalar-restriction definition, which keeps the underlying additive maps. The functor and lambda are obtained from that localization property. The shift identity is checked on complexes, and the compatibility equation is uniquely determined after localization. This is a direct use of a defining universal property, not a hidden appeal to an additional derived-functor theorem. I checked the direction of lambda: it is the inverse orientation of Mathlib mapDerivedCategoryFactors and exactly the orientation in the item.

Step 3 cites def-pur-sheaf-tensor-product for the sectionwise tensor followed by sheafification and def-weil-presheaf-modules-sheafification for the extension/uniqueness property. The latter explicitly constructs the underlying abelian sheafification and the unique extended scalar action. Consequently the sectionwise inverse maps remain inverse sheaf maps, including their S-action. I wrote the balancing identity, restriction compatibility, inverse formulas and differential equation. This is an elementary swap with a degree-zero factor, not a general theorem about total-complex symmetry or a second node restating this clause.

Step 4 cites exactly the K-flat-computation clause of lem-pur-derived-change-of-rings. It applies to the given f:P to G, not just the identity resolution. The second citation, def-weil-sheaf-of-modules-category, says that the small-site module categories are abelian. The site's smallness, commutativity of the three ring sheaves, K-flatness of P and its flat terms are all available. F sends e inverse to an isomorphism with the stated source, so the displayed eta has the required orientation. The same proof applies to wu and T.

Step 5 uses only the established maps and cancellation of inverse pairs, so has no additional node citation. The result is an isomorphism in D(A); no unsupported equivalence of coefficient categories is used.

Step 6 cites the same tensor/sheafification definitions and the restriction definition; the latter really gives the v- and w-induced A-actions. A-linearity of h implies B-linearity through u, and I wrote that equation before tensoring. The A-linearity and cochain-map equations hold before sheafification; both swap-square composites have the identical formula on pure tensors. Equality then follows by additivity on presheaves and uniqueness on sheafification, rather than asserting that all sections of the sheaf tensor are pure tensors. Products, units and S-linearity of h are never required.

Step 7 uses only the already proved square and the definitions of delta, so has no additional node citation. I wrote its localized conjugation formula with all lambda and eta factors. This explicitly avoids treating a map between different coefficient categories as an S-linear cochain map to which lambda's usual naturality would apply. The formula is the claimed map on the fixed scalar-last models, without asserting any extra natural transformation in K beyond the item.

I checked the edge cases P=0, empty site, identity scalar maps and zero ring sheaves: every construction is still defined and every asserted isomorphism remains an isomorphism. For a genuine non-ring coefficient map on the one-point site, take B=A=S=T=Z and h multiplication by 2 (or h=0): both square routes give p tensor 2s (respectively zero), even though h does not preserve 1. For a nonflat coefficient map take Z to Z/2 and a free K-flat resolution; the argument still computes the derived extension, and restriction's exactness does not require that map to be flat. Unbounded P causes no tensor-totalization convergence issue: the coefficient is in degree zero and the differential is written termwise. No completeness was used.

I checked delivery-errors B--E point by point: no new-node format or duplication issues arise; statements/dependencies and imported metadata are retained; each citation supplies the exact fact used; non-elementary exactness and K-flat computation have cited statements; no circular dependency is introduced; the final map equality is written explicitly. All proof steps are below 2000 characters (the longest is 1014), and none hides a lemma being asserted without argument. The few-line constructions remain steps rather than artificial nodes. Citation quotations were checked as literal substrings. No Lean file was written and no compiler, Lake or local DAG-validation script was run.

## Unfinished work

No mathematical work remains for this one-level split. The independent maintainer review and subsequent stages remain the project's responsibility.
