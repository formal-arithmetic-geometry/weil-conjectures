## Worker report

Files written:
- dag/nodes/sec-poincare-duality/lem-pod-pullback-identities-scalar-extension.json: statement, split into five proof steps, no Mathlib match.
- citations.json: a verbatim statement quotation for every dependency cited by every step.
- searches.jsonl: actual searches made with msearch.py; inherited searches in the item retained.

## New nodes

None. There are 0 new nodes and 0 new Mathlib leaves. The existing DAG already has the substantive realization and comparison lemmas. In particular, I did not create a node restating either of the item's two clauses.

## Attachments

None. The exact blueprint-tag search in lean/WeilConjectures found no declaration. Searches by pullback/scalar/composition/inverse found ordinary sheaf, field-coefficient and finite-coefficient results, including SixFunctors/ProEtale/FieldCoefficient/ExtendScalarsComp.lean and ModuleObject/Derived/UpperStarCoherence.lean. They do not state both identities for the specified completed integral constructible functors. Existing sorried Sheaf declarations were not counted as finished proofs.

## Literature wanted

None. The proof is explicitly agent-written: the blueprint requires this coherence implicitly; I do not attribute the completed coefficient identities verbatim to a numbered Stacks or Bhatt--Scholze theorem.

## Statement corrected

STATEMENT-DISPUTED: the imported references to "the isomorphisms" did not fix their normalization. The cited existence statement lem-weil-isomorphism-derived-pullback alone permits arbitrary natural isomorphisms. For a concrete test take ell = 3, E = Q_3, a proper finite extension L, g = id on a geometric point, K the regular completed coefficient object, and the canonical alpha. Choose lambda at E to be multiplication by -1 and lambda at L to be the identity (both natural isomorphisms satisfying the cited existence statement). Because bar g = g, the displayed epsilon at E is multiplication by (-1)^2 = 1, so this particular same-map test cancels the sign and is NOT a counterexample. Instead use a nonidentity scheme isomorphism g between two separately labelled isomorphic geometric points X and Y. Choose lambda for g at E to be -1, for bar g at E to be +1, and both lambdas at L to be +1. Then epsilon^E = -1 and epsilon^L = +1. The claimed scalar identity would say +1 = -1 on the nonzero L-coefficient object. Thus existence alone cannot fix the identity.

The repaired statement specifies lambda = kappa inverse, where kappa is the already defined zero-shifted-coordinate quotient-cone map; the existing normalization node proves that this map is invertible on complete objects. It also specifies the existing whole-system realization families for c and alpha. These choices realize the source's intended canonical inverse automorphism and composition maps, not a new hypothesis on schemes, coefficients or complexes. Both clauses, all schemes with ell invertible, and the entire constructible complete domain are retained. Literal backslash-n characters in the imported statement were changed to paragraph breaks.

## Blueprint and duplicate searches

Read dag/chapters/sec-poincare-duality.json, dag/units/sk-lem-finite.json and the three-level rule in SETUP.md. The item's nearest blueprint ancestor is prop-weil-operations, through lem-pod-semilinear-field-operation-lifts. Its proof sentence 1 invokes lem-fix-weil-operations; the latter's first paragraph invokes pullback commutation and identity pasting with the inverse automorphism square. Those exact places are recorded in split_report.blueprint. This supplies a coherence tool below that route, without changing a chapter or unit.

Ran tools/blueprint_refs.py ancestor for the item and whole-blueprint searches for "pullback scalar", "completion", "inverse image", "scalar extension", "inverse identities", "pullback composition" and "inverse-image comparison". Read the existing candidate statements; no imported blueprint node states the entire item. Searched the whole DAG for comparison, scalar, completion unit, kappa/lambda and inverse-image concepts. This found lem-trf-integral-pullback-comparison-realization for clause (1) and lem-weil-isomorphism-comparison-scalar-extension for the primitive square needed for clause (2). The latter does not already state inverse-identity pasting: Steps 3--5 actually prove that consequence. No new node was needed and no tag-sharing new/existing pairs need a Not duplicates entry.

## Mathlib searches

Read every hit of the seven logged msearch.py calls. The initial Loogle query contained the unknown identifier CategoryTheory.Functor.LeftDerived; this was recorded as a rejected query, then repaired by querying PresheafOfModules.pullbackComp alone. LeanSearch and both LeanFinder calls returned usable responses; none was marked unavailable. The two semantic phrasings distinguish the geometric completed question from general scalar and adjunction coherence.

Candidates checked in the pinned Mathlib source: PresheafOfModules.pullbackComp, pullback_assoc and identity laws in Algebra/Category/ModuleCat/Presheaf/Pullback.lean:131--158; SheafOfModules.pullbackComp and pullback_assoc in Sheaf/PullbackContinuous.lean:167--200; ModuleCat.extendScalarsComp, extendScalars_assoc and extendScalars_id_comp in ChangeOfRings.lean:984--1054; CommRingCat.moduleCatExtendScalarsPseudofunctor in Pseudofunctor.lean:61--72; the free/unit pullback comparison in Sheaf/PullbackFree.lean. These are ordinary module or sheaf constructions, with no derived-completion or strict-system realization normalization. They therefore do not specialize in one line to the item. The second Mathlib grep under CategoryTheory/Sites returned no hits. Exact queries and verdicts are appended to mathlib_searches; the earlier two inherited grep records remain intact.

## Review by Q18

I read the current main-20261015 blueprint files prop-weil-operations.proof.md and lem-fix-weil-operations.proof.md, and the integral/common-stage paragraph of def-weil-derived-pullback-tensor-hom.md. For the underlying construction I read Stacks 0D6D (sites-cohomology.tex, lemma-derived-pullback-composition), 099N(2),(5) (proetale.tex, lemma-pushforward-Noetherian-case), 03D6 (sites-modules.tex, definition-pushforward) and 08TC (derived.tex, definition-derived-limit), verifying the tag/label map. I also read Bhatt--Scholze Lemma 6.5.9(4) and Remark 6.5.10, PDF pages 50--51. Its qcqs hypotheses are not silently applied to arbitrary schemes: the proof uses the existing arbitrary-scheme normalized comparison statements, whose refinements are agent-written. No SGA source or alternative purity route is used.

For Step 1 I opened lem-trf-integral-pullback-comparison-realization. Its statement has exactly the displayed a/c composition equation and explicitly identifies those families with the integral composition and scalar comparisons cited by the item. Its hypotheses are finite E subset L, schemes with ell invertible and a constructible complete K, and explicitly impose no finite Tor amplitude. All hold here. I cite its statement, not its proof or only its evaluation at individual quotients.

For Step 2 I opened lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback and lem-weil-isomorphism-derived-pullback-comparison-normalization. The first supplies the exact equivalence and sectionwise model, the second both constructible membership and a natural comparison, and the third supplies invertibility of the SPECIFIED kappa, not an unspecified lambda. The same hypotheses hold for bar g and for both coefficient fields. These facts ensure that every object fed to a later beta or lambda remains in the full constructible complete category. The distinction between the existence theorem and the specified normalization was the correction described above.

For Step 3 I opened lem-weil-isomorphism-comparison-scalar-extension and copied its actual alpha T(kappa) = kappa beta equation into citations.json. Taking inverse kappa is now legitimate by Step 2. Multiplication on the two sides of this equation gives the lambda square, once for g and once for bar g. This is elementary cancellation of already cited invertible arrows, not a new lemma.

For Step 4 I read the complete beta definition and its local b formula in that same scalar-comparison node, the natural chi isomorphism in lem-weil-finite-free-completed-scalar-comparison, and the sectionwise inverse-image formula in lem-weil-proetale-isomorphism-inverse-image. On an object (U -> X), reindexing first by g and then by bar g is the identity on both the coefficient section and the module section. This proves the b counit equation on the same complexes; I do not claim that equality of maps into a derived limit can be checked on projections. Substituting beta = G(chi) b chi inverse cancels adjacent chi factors. Naturality of u and chi gives the exact displayed beta counit equation. This elementary two-line tensor/conjugation calculation is written out; it requires neither tensor commuting with arbitrary inverse limits nor flatness of any finite quotient map.

For Step 5 I checked each intermediate functor: alpha^g goes from T_X P_E to P_L T_Y; naturality of lambda for bar g moves it through Q_L; the bar-g square is evaluated at P_E K; naturality of beta for bar g is evaluated at lambda^g_E:P_E K -> G_E K. After that the initial triple is exactly Step 4, leaving T_Y of the definition of epsilon^E. Thus no unidentified "transport" or compatibility with connecting maps is left implicit. The only new work in Steps 3--5 is cancellation and naturality from these explicit statements. Every step is below 2000 characters and no long proof step hides a lemma.

Small cases checked: K = 0; E = L (chi is the canonical completeness map under multiplication, so the comparisons become identities); g = id and bar g = id (both lambda factors have the same fixed canonical normalization); nonidentity g and its separately labelled inverse (checking that H G is the functor on Y, not on X); arbitrary ramification index greater than one. The argument does not assert that the quotient map A_E,n -> A_L,n is flat. The tensor calculation uses the finite-free completed coefficient extension from the cited scalar node. The unnormalized sign test in Statement corrected shows why the canonical-choice correction matters.

I checked B--E against the written files: no unsplit nodes, hollow definitions or new notions have been introduced; TeX uses single decoded backslashes; all references are to statements that contain the needed formulas, with verbatim quotes; proof_deps is exactly the union of uses. Read-only reachability checking found no dependency path from a cited tool back to this item. All six off-unit dependencies are declared as generic tools in split_report.tool_uses, with reasons; the maintainer still decides those uses. The report and split retain the existing blueprint provenance and imported metadata.

## Unfinished work

None in the mathematical split. Lean implementation and proof are outside this stage-1 delivery. Required server dry run and push are performed after this report is written.
