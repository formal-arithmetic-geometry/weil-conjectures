# Stage-1 report: det-prop-closed-adjoint-constructible-support

## Files written

- `dag/nodes/sec-six-functors-basics/det-prop-closed-adjoint-constructible-support.json`: statement, split; item statement unchanged; retained the seven-step localization route and inherited searches. Replaced the long inline counit comparison by a generic lemma and made the quasi-compactness inputs explicit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-orthogonal-triangle-counit-normalization.json`: new statement-only lemma, unsplit, no Mathlib match after the recorded searches. This is a formal comparison for an arbitrary fully faithful functor with right adjoint and an orthogonal triangle; it has no sheaf or constructibility assertions.
- `citations.json`: verbatim statements backing every use in the item's numbered proof steps.
- `searches.jsonl`: preserved searches from the interrupted attempt; their results were read, not rerun merely because the provider interrupted the turn.

## Attachments

None. A search of `WeilConjectures/` in the read-only slopmaster2 source for the blueprint id found no declaration. Concept searches found general pro-etale closed-support functors in `SixFunctors/ProEtale/Derived/ClosedImmersion.lean`, stability results in `SixFunctors/ProEtale/Derived/Stability.lean`, and etale open-closed triangles in `SixFunctors/OpenClosed/Derived.lean`. Those do not state all clauses of this result for the pulled-back condensed field module categories. In particular the etale triangle has the extension-by-zero orientation and different coefficient categories. No exact project declaration was found for the new generic counit-normalization statement either. Upstream master is reference material, not evidence of a finished proof.

## WANTED

None. The blueprint and the Stacks sources needed here are available locally.

## Corrections and scope

The sandbox's previous work survived the interruption. I compared its item with the current repository: the statement, blueprint ancestry, unit binding, and seven-step route agree; the repository still has status `unsplit`. I retained the earlier proof, citations and searches, and completed the missing report. The former step 4 was a long independent categorical comparison. The human's long-step rule applies: it is now the statement-only generic normalization node, not an unlabelled lemma hidden inside a step. Every remaining step is shorter than 2000 characters.

I also removed step 1's reliance on an unstated compactness theorem for basic affine opens. Existing nodes now supply open-subscheme Noetherian permanence, local-Noetherian quasi-separatedness, and qcqs morphism permanence. These are generic tools declared in `split_report.tool_uses`, not replacements of the unit's localization route. No existing node other than the assigned item is edited, and no unit/chapter route or target statement is changed. The assigned node is a detail of the unit's first step, not its key statement, so no unit realization fields are changed.

The blueprint's first paragraph attributes the sequence with supported kernel and `j_*j^*` to Tag 09AH. Reading `proetale.tex`, `lemma-ses-associated-to-open` shows that 09AH itself states the other short exact sequence, with `j_!j^{-1}` and `i_*i^{-1}`. I therefore do not take the supported-kernel or injective-surjectivity assertion from that tag. Step 3 uses the existing `det-lem-formal-closed-support-derived` statement, which explicitly gives the required triangle, adjunction, unit arrow and fiber formula. This preserves the result and route without repeating the blueprint's inaccurate attribution. The latter statement does not label the first arrow as the counit; that is precisely why step 4 proves the comparison separately. No statement dispute or weakening of the assigned statement is needed.

## Mathlib and duplicate searches

The saved `searches.jsonl` contains the actual leanfinder, loogle, leansearch and Mathlib grep queries, including two semantic phrasings for each claim. The new lemma's seven searches are copied with their exact tool/query texts and actual hit lists. All services in those seven entries ran. For the item, one Loogle query returned an unknown-identifier diagnostic; the diagnostic is retained, and a later valid `DerivedCategory.triangleOfSES` query ran. No unavailable service is represented as evidence of absence.

I read the returned Mathlib sources: `CategoryTheory/Triangulated/Adjunction.lean` proves that adjoints of triangulated functors are triangulated; `CategoryTheory/Triangulated/Orthogonal.lean` gives orthogonality/localization facts; `CategoryTheory/Adjunction/FullyFaithful.lean` gives invertibility of counits on objects already in the essential image. None proves that the transpose of the first arrow in the specified orthogonal triangle is invertible and transports that triangle to the specified counit triangle. The homEquiv hits are adjunction formulas, not the triangle-normalization statement. `AlgebraicGeometry/Sites/ElladicCohomology.lean` and the pro-etale-site hits construct sites/coefficient sheaves, not the full bounded-constructible supported-sections assertion. Thus neither claim is a one-line specialization of a hit and no new Mathlib leaf is claimed.

DAG searches by tags 0149 and 0037 and by counit/triangle/orthogonal/adjoint keywords were read. Whole-blueprint searches `orthogonal triangle counit normalization` and `constructible support` have no matches. A broader `counit` search locates many geometric counit constructions, not this general normalization lemma. The ancestor command gives the assigned blueprint id itself. The new lemma's `from.place` names the final sentence of the first proof paragraph, and both nodes have `same_as: []` because no other blueprint node states the same result. The existing formal-support nodes are reused, not recreated.

## Not duplicates

lem-sfb-orthogonal-triangle-counit-normalization vs lem-pc-perfect-hom-triangle-row-presentations: the latter identifies five-term Hom rows over a scheme and their presentations, not a triangle arrow with an adjunction counit.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-hom-into-triangle-exact: Hom exactness is an input to the generic normalization argument, but says nothing about an adjunction, invertibility of a transpose, or the resulting triangle isomorphism.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-quasi-inverse-adjoint: the latter constructs adjunctions from an equivalence; here the functor is only fully faithful and the argument uses an orthogonal third triangle object.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-adjunction-of-natural-bijection: the latter gives the unit/counit formulas from natural Hom bijections; it does not assert invertibility of the transpose of an arbitrary distinguished-triangle arrow.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-adjunct-counit-identity: the adjunct equation supplies the equality of first arrows, but does not give invertibility of that adjunct or any distinguished triangle.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-triangle-morphism-extension: the latter extends or identifies morphisms between triangles under different Hom-vanishing assumptions; it does not identify the first arrow using an adjunction and its fully faithful left functor.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-hom-out-of-triangle-exact: the latter is contravariant Hom exactness, without any adjunction or counit-normalization assertion.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-weil-pbc-adjunction-ext: the latter compares two adjunction structures by equality of units/counits, not a distinguished triangle with an unspecified first arrow.

lem-sfb-orthogonal-triangle-counit-normalization vs lem-cbc-kan-realization-mapping-classes: the latter compares simplicial and topological mapping classes; a shared source tag does not make it a categorical triangle-normalization lemma.

## Review by Q155

I read the current main-20261015 chapter record, the unit `sk-prop-closed-adjoint-constructible`, and the assigned statement and both proof paragraphs. The item realizes unit step 1: localization, open-direct-image finiteness, triangulated closure, and closed pullback. The Yoneda comparison of unit step 2 remains in its existing separate node. The explicit separated finite-type setting agrees with the chapter's standing setting. I checked both permitted condensed coefficient rings, including the finite-subextension definition of the algebraic-closure ring, against the definition nodes; no discrete constant coefficient category is substituted.

For the item I read Stacks `morphisms.tex`, Tag 01T6 (`lemma-finite-type-noetherian`); `properties.tex`, Tags 01OW, 01OY, 01OZ; `schemes.tex`, Tag 03GI (`lemma-quasi-compact-permanence`); and `proetale.tex`, Tags 09AA (`lemma-closed-immersion`), 09BM (`lemma-closed-immersion-complement-retrocompact-exact`) and 09AH (`lemma-ses-associated-to-open`). For the new generic lemma I read `derived.tex`, Tag 0149 (`lemma-representable-homological`), and `categories.tex`, Tag 0037 (`definition-adjoint`) and the following unit/counit formulas. The new statement is an agent's extracted formal lemma serving the blueprint's counit-identification sentence, not a verbatim claim that Stacks states the whole lemma.

Step 1: `sk-def-sfb-dc-setting` supplies finite type over the field; `def-weil-pbc-noetherian-ring` makes the elementary two-ideal check sufficient for the field; `pqf-def-locnoeth` gives the affine covering definition. `lem-weil-pbc-finite-type-over-noetherian` gives Noetherian X and Z. I read the additional three cited statements: `lem-weil-pbc-noetherian-open-subscheme-noetherian` explicitly gives quasi-compact U; `lem-weil-pbc-locally-noetherian-quasi-separated` gives quasi-separated X; and clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` says that a morphism with quasi-compact source and quasi-separated target is quasi-compact. Its source and target hypotheses are now both supplied, rather than assumed from finite type without explanation.

Step 2: `sk-def-sfb-coefficient-morphisms` explicitly says alpha_f is a ring-object isomorphism. `sk-def-sfb-module-pushforward-pullback` gives the module functor with extension along that isomorphism. The statement of `lem-weil-pbc-proetale-immersion-limit-preservation` includes exactly this module extension-along-an-isomorphism case, exactness, and its scalar action. `sk-def-sfb-derived-categories` explicitly identifies derived exact functors with their termwise functors. Thus the notation i^*, j^* is justified for the module-object derived categories, with no assertion about extension along an arbitrary ring map.

Step 3: I opened `det-lem-formal-closed-support-derived` and its sheaf-setting dependency. Clause (1) supplies the right adjunction, clause (3) supplies the natural distinguished triangle and labels its second arrow as the unit, and the final displayed formula supplies the closed pullback of the fiber. The Noetherian standing setting and admissible fields are those of steps 1 and 2. The step does not take a counit label that is absent from the cited statement.

Step 4: `lem-weil-pbc-proetale-ringed-open-closed` explicitly states exact i_*, i^{-1}i_*=id, and j^{-1}i_*=0 for a quasi-compact complement and inverse-image ring coefficients. Step 1 verifies that complement hypothesis; step 2 identifies those rings with the actual pulled-back condensed coefficients. The exact-functor clause of `sk-def-sfb-derived-categories` gives the identities termwise, and `sk-def-sfb-module-derived-pushpull` supplies both derived inverse-image/direct-image adjunctions. The Hom bijection proves full faithfulness of i_*; the other one computes Hom(i_*A,Rj_*j^*K)=0. Termwise i_* commutes with shifts, so the same vanishing applies to B[-1]. These verify every hypothesis of the new generic lemma with F=i_*, G=R Gamma_Z, and B=Rj_*j^*K. Its formula preserves the second arrow and identifies the first arrow with the actual counit by an isomorphism, not merely by naming the first arrow a counit.

Step 5: `lem-sfb-dc-upper-star-preserves` explicitly gives bounded-constructible pullback for every morphism in the standing setting, and `lem-sfb-dc-lower-star-preserves` explicitly includes both underlined E and underlined algebraic-closure coefficients. The setting assumes X, U, Z separated finite type and all maps over k, so applying them to j requires no additional geometric hypothesis. The direct-image node is bound to the prescribed open-coefficients unit. Its existing metadata has older external references; this delivery uses its statement and the blueprint route, and introduces no prohibited source route.

Step 6: `det-cor-coefficient-heart-ii-triangulated` states exactly two-out-of-three, shifts, and isomorphism closure for Noetherian schemes with these field coefficients. It applies to X from step 1 and the triangle from step 3, giving the supported pushforward and its shift. Neither integral coefficients nor a closure theorem for a different constructibility predicate is used.

Step 7: the same pullback statement applied to i gives bounded constructibility of i^*F. The exact fiber formula is a displayed clause of `det-lem-formal-closed-support-derived`, so this identification is available from a statement, not from its proof. The isomorphism-closure clause applies on Z because finite type over the Noetherian field gives Noetherian Z, as already checked in step 1. This gives the claimed supported complex itself and completes every clause of the item.

For the new lemma, I checked the statement on identity adjunctions, the zero object and the zero subcategory, and triangles with B=0. Its proof plan, recorded here rather than smuggled into the unsplit statement, is: Hom(FA,-) exactness and the two vanishings make postcomposition with a bijective. Full faithfulness and the specified adjunction identify this bijection with h mapped to u composed with h on Hom(A,GK). At A=GK, surjectivity gives v with uv=1, and injectivity applied to u(vu)=u gives vu=1. The adjunct formula gives a=epsilon_K F(u). The three squares for (F(u),1,1) commute with the last arrow changed to F(u)[1] composed with d, so the triangle isomorphism axiom proves the normalized triangle distinguished. Only pre-triangulated axioms are needed; the source category need not itself have a shift. The sign/direction of the new connecting arrow was checked against the last square.

The two orthogonality hypotheses are both needed: allowing only Hom(FA,B)=0 would prove surjectivity without injectivity. In the application, both are established using shift compatibility. Empty Z or empty U causes no failure: the former has zero supported object, and the latter has B=0; K=0 also gives the zero triangle. No finiteness bound is imposed on a previously unbounded ambient object except where K or its image is proved bounded constructible. Each new lemma object and hypothesis is introduced explicitly, no proof is in its statement, and the lemma contains strictly less geometry than the assigned statement rather than restating a constructibility clause. Every cited statement has a verbatim record in citations.json. I checked delivery-errors B through E, especially C1/C4 and the duplicate tests, with these files open.

## Unfinished work

The one new generic lemma is intentionally statement-only and joins the stage-1 queue. Nothing in the assigned item's seven-step argument is left as an unnamed claim. No Lean was written and no compiler, Lake or build command was run.

## Validation

A server-only `review_split` check before completing the report returned PASS. The required deliver.py dry run and push are the final validation and delivery steps; their process output determines delivery success.
