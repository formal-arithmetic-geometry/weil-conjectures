# Stage-1 report: lem-sfb-integral-derived-extension-comparison

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-integral-derived-extension-comparison.json`: statement, split; five proof steps over existing nodes. Statement and statement dependencies retained, as are all inherited metadata and searches.
- `citations.json`: fifteen verbatim statement excerpts, one for every step/node citation.
- No new nodes, no new Mathlib leaves, no unit edits. The item is a supporting node of the rationalization unit, not its key statement.

The sandbox also holds the exact search log, a local text extraction of Bhatt–Scholze, and the script used to write the item. These are working materials, not additional DAG changes.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag, integralScalarExtension, padicIntegersToPadicSubfield, and boundedConstructibleExtendScalarsCompatibility found no declaration stating all the item’s clauses. `AlgebraicGeometry.ProEtale.boundedConstructibleExtendScalarsCompatibility` in `CategoryTheory/ModuleObjects/EllAdicRationalization.lean:138` gives only the specified restriction isomorphism; the preceding preservation lemma contains sorry. The generic exact-functor comparison and Mathlib’s termwise triangulated functor are only constituent results, not an attachment of this item.

## WANTED

None. All source documents used are available locally.

## Problems found and corrected

The imported item had no proof. Its statement is consistent with the current source route, so I did not alter it. In particular, the source category here is the existing ordinary bounded constructible category defined using stratified locally finitely presented internal modules. I did not replace it by a derived-complete category, discrete coefficients, or a smaller category of lisse sheaves.

A tempting citation of sk-def-sfb-bounded-constructible alone would have missed its explicit Serre-closure hypothesis. Step 4 therefore invokes the actual integral constructible Serre theorem and the general bounded-cohomology triangulated-subcategory theorem. Likewise, the natural isomorphism to D(T) alone does not specify shift compatibility: step 3 writes down the transported shift comparison, and step 5 uses the analogous comparison for the specified restriction isomorphism.

The split avoids det-prop-sfb-qlbar-colimit-x-invert-ell as an intermediate dependency: its present proof uses continuous-constructible-integral-image, a result about an image which is unnecessary for exactness here. The direct existing continuous-integral-scalar-exact theorem already states exactly the needed finite-limit preservation. This also keeps the proof independent of the bounded-constructible localization theorem which uses this item.

## Unfinished work

None within this one-level split. The cited unsolved nodes remain the existing DAG’s obligations; none was silently treated as a finished Lean proof. No Lean file was written and no compiler, Lake, or build command was run.

## Search and reuse

I read the chapter and rationalization unit records, the current ancestor thm-sfb-extend-scalars-localization and its first proof step, and the current blueprint’s restriction and point-inclusion nodes. Whole-DAG searches by exactness, derived-functor, termwise, constructible closure, and corresponding titles found the existing results used here. `tools/blueprint_refs.py ancestor` identifies thm-sfb-extend-scalars-localization as the ancestor; whole-blueprint searches for integral-derived-extension and termwise found no node stating this entire combination. The item has same_as = []. No duplicate node was created.

Five logged Mathlib searches were run for Q43: LeanSearch, Loogle, grep, and two different LeanFinder phrasings. I read their returned results. The broad categorical phrasing returns mapDerivedCategory, mapDerivedCategoryFactors, its CommShift instance, and its IsTriangulated instance. I read Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean, in particular lines 36, 41, 80 and 104. These supply the generic termwise functor and its triangulated structure, already represented by the existing Mathlib leaf lem-weil-pbc-exact-functor-derived-factorization. They do not give the actual continuous integral coefficient inclusion, exactness along it, or the required integral constructible Serre theorem. The narrow phrasing returned unrelated condensed/module and continuous-linear-map declarations. All inherited search records were retained and each new record reproduces a query actually present in searches.jsonl.

## Not duplicates

No new nodes. In particular, I reused lem-weil-pbc-continuous-integral-scalar-exact, lem-sfb-preserving-colimits-additive, def-sfb-left-derived-exact, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-integral-constructible-serre, and prop-weil-pbc-module-bounded-constructible-triangulated instead of creating versions of them.

## Review by Q43

I read Bhatt–Scholze §6.8, especially Definition 6.8.10 and Proposition 6.8.11(1),(3) on pages 60–61, and Proposition 6.8.14(2) on pages 61–62. The latter is the parent localization’s route; this item supplies its preparatory comparison, rather than trying to reprove or cite the localization itself. I also read Stacks derived.tex, Tag 014X (lemma-additive-exact-homotopy-category) and Tag 015F (lemma-right-derived-exact-functor), and the Mathlib exact-functor source described above. The item’s proof is marked agent-written because it assembles these existing statements and the internal-module identifications rather than copying a proof of this exact combined assertion from the paper. There are no new-node sources to review.

For step 1, I opened the statements of def-sfb-integers-to-subfield-point, def-sfb-integers-to-subfield, def-weil-pbc-continuous-integral-coefficients, and sk-def-sfb-derived-extension-of-scalars. They specify respectively the postcomposition inclusion on continuous functions, its pullback along p_X, the actual continuous inclusion and the name integralScalarExtension, and total left derivation of extension. The induced norm in the item makes its valuation ring precisely the closed unit ball used by the continuous model. Identifying the two pointwise maps and applying the same pullback is elementary; no theorem about the behavior of a different coefficient category is used. I checked these formulas against the inclusion in EllAdicRationalization.lean and the actual definitions in Sheaf/Paper/ContinuousIntegralCoefficients.lean.

For step 2, the continuous-integral-scalar-exact statement explicitly preserves finite limits on arbitrary internal module sheaves on every scheme. It assumes only the prime and a normed field algebra, satisfied here. Clause 2 of sk-def-sfb-change-of-scalars explicitly supplies finite-colimit preservation, and lem-sfb-preserving-colimits-additive supplies additivity. I did not infer tensor exactness merely from a definition of flatness. These citations cover every non-elementary assertion of the step.

For step 3, def-sfb-left-derived-exact explicitly supplies the canonical LF ≅ D(F) comparison for the total derived functor in question; its existence is part of the functor already specified in the item. The exact-functor-derived-factorization statement explicitly supplies termwise descent and a triangulated shift comparison, not just fully faithfulness of a localization. I checked the shifted comparison’s direction: L(K[1]) maps through alpha to D(T)(K[1]), then to D(T)(K)[1], then back to L(K)[1]. Naturality gives an isomorphism of whole image triangles, and conjugating sums gives additivity. The definition of triangulated functor includes invariance of distinguished triangles under isomorphism. No comparison between shifts was omitted.

For step 4, I read both cited closure/subcategory statements, not their proof dependency lists. The integral Serre result requires finite normed E and a topologically Noetherian underlying space, exactly the item’s assumptions, and states closure for the same stratified pro-etale locally finitely presented internal module predicate. The generic triangulated-subcategory proposition assumes precisely those closure properties; zero and isomorphism invariance hold by definition. Its bounded cohomology subcategory matches sk-def-sfb-bounded-constructible, whose statement expressly imposes no derived completeness. Thus the application neither assumes the scheme is Noetherian as a ringed space nor inserts a finiteness-of-dimension hypothesis. These two off-unit statements are declared as generic tools in split_report.tool_uses, alongside actual scalar exactness; they implement the unit’s existing route.

For step 5, def-sfb-bounded-constructible-extend-scalars explicitly states the action on objects and morphisms and the identity components of the specified compatibility isomorphism. I used those components, fullness and faithfulness of the inclusion, and the already established results of steps 3–4. The naturality equation is written for all three arrows, with the final arrow using the transported shift comparison. This elementary restriction calculation proves the compatibility actually requested, without assuming the target full subcategory is already triangulated. Its source-triangle inclusion uses the inherited structure from step 4.

I checked delivery-errors B–E: no new unsplit nodes, missing notions, duplicate lemmas, restated-clause children, or Mathlib facts disguised as new obligations; no non-elementary step is left uncited. Each cited statement was reopened and citations.json contains a verbatim portion of its relevant assertion. No proof depends on the parent theorem. I corrected composition-order notation while writing the comparisons. Every step has fewer than 2000 characters and none hides a separate comparison lemma. Empty X, the zero complex, the identity triangle, and E = Q_l cause no exceptional case: exactness is on arbitrary module objects, zero is constructible, and the restriction comparison remains the identity. No assumption of nonempty X, unramified E, invertibility of ell on X, a field base, or boundedness of ambient complexes enters. No SGA source is cited.
