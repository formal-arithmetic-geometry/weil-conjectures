## Worker report

Item: lem-per-rational-scalar-completion-unit-square. Group: Q79. Stage 1 only, 2026-10-22.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-scalar-completion-unit-square.json — statement, now split into seven proof steps; unchanged statement and statement dependencies; no Mathlib match.
- citations.json — a verbatim statement quotation for every dependency of every proof step.
- report.md and searches.jsonl — this report and the actual search log. prepare.py is sandbox-only preparation material.

## New nodes

None. The completed-unit square assembles existing, more general tools. In particular, lem-weil-pbc-finite-free-completion-transport already states the ambient comparison, its actual unit equation, identity normalization and coefficient-tower law. Creating a further finite-free exchange lemma would duplicate it. There are zero new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, scalar/completion and completion/unit phrases, and scalar/pullback notions. The ordinary weakly-etale, Z_l-to-Qbar_l comparison in SixFunctors/ProEtale/Adic/PadicIntModuleUpperStar.lean:277–284 is a different statement: it does not cover arbitrary g, finite ramified coefficient extensions, unbounded completed module pullback or the specified quotient completion units. No project declaration found states every clause of this item. No compiler or Lake command was run.

## WANTED

None for this split. The existing local-field nodes retain their own documented source obligations; I do not claim to have read Serre's unavailable book.

## Audit and changes

The imported item was statement-only. I preserved its complete statement, its statement dependencies, provenance and inherited search results. I supplied the proof rather than moving any of its clauses to new statement-only nodes. Each step is shorter than 2000 characters. The only elementary step is the displayed substitution of the completion-unit equation followed by naturality. The non-elementary K-flat, reflector, preservation and pasting inputs are named existing nodes.

I read the current main-20261015 blueprint files for lem-per-smooth-pullback-t-exact and prop-weil-pbc-scalar-extension, the chapter and curve-perverse unit, and the parent lem-per-rational-realization-scalar-coherence. The nearest blueprint ancestor and its via chain are retained. Whole-blueprint searches for “completion unit”, “finite free completion”, “unit-normalized”, “finite-free scalar”, “scalar extension” and “completed pullback” found the general scalar-extension and completed-pullback nodes, but no other imported statement identical to this square. The generic scalar-extension node supplies the wider context, rather than being used as a substitute for the unit calculation.

Mathlib searches were run using msearch.py and their actual results are appended to the inherited records. The first Loogle query used an unknown unqualified identifier Reflective; its record explicitly says invalid query and makes no absence inference. The replacement query CategoryTheory.Adjunction, CategoryTheory.Functor returned ordinary adjunction declarations. The first LeanFinder phrasing returned ordinary adic-completion declarations; the second returned ModuleCat.extendScalarsComp and its ordinary associativity/unit laws. LeanSearch returned SheafOfModules.pullback, pullbackPushforwardAdjunction and related ordinary sheaf constructions. I read PullbackContinuous.lean:44–65 and AsTensorProduct.lean:316–348: their adjunction and finite-Noetherian ordinary-module adic-completion result do not state this unbounded derived sheaf comparison or identify its completion units. Thus neither the item nor a newly needed auxiliary lemma is a one-line Mathlib specialization; no auxiliary lemma is newly created.

## Not duplicates

No new nodes. Existing finite-free completion transport, reflected squares, ringed monoidal calculus and constructible scalar transport are cited directly. I also read lem-pur-finite-free-completion-exchange, which uses quotient/Roos models and extra exact-product/regularity hypotheses: the existing Koszul-reflector transport is the direct general input here, so the proof does not silently assume those extra hypotheses.

## Review by Q79

I read algebraization.tex at Tag 0A0E, label lemma-derived-completion-koszul, and Tags 0A0G and 099J, labels lemma-pushforward-commutes-with-derived-completion and lemma-pushforward-derived-complete. The former models the reflector on arbitrary complexes; the latter gives the canonical pushforward/completion arrow by its universal property, including its unit normalization. I read sites-cohomology.tex at Tags 0G7E, 07A4, 0D6D and 07A6 (lemma-pullback-K-flat, lemma-pullback-tensor-product, lemma-derived-pullback-composition, lemma-adjoint). These justify using flat-term K-flat pullbacks, composing them, and using the specified derived adjunctions. I also read Bhatt–Scholze, Lemma 6.5.9 on printed pp. 50–51, Proposition 6.6.11 on p. 54, and the opening of Lemma 6.8.2 on p. 58. The sharper ordinary-pullback/actual-unit clause used in step 6 is taken from the existing realization/pullback node, not asserted to follow from Lemma 6.5.9 alone. No new node has a source requiring an additional review.

Step 1 uses the finite-free completed scalar node for its explicitly stated rank, the absolute-value node for uniqueness, and the DVR node for factorization and unit absolute values. Restriction of the L-absolute value is an extension of the same Q_l absolute value, so uniqueness applies to E. Since the old uniformizer has absolute value strictly between zero and one, its exponent in L is positive. This is where ramification is checked; e=1 is never assumed. The inverse of the constant unit remains an inverse in the completed sheaf.

Step 2 uses the finite-free completion-transport statement itself: it gives a natural isomorphism on all ambient complexes, the equation with eta, its identity value and its coefficient-tower equation. Its finite-free and positive-power hypotheses were checked in step 1. The constant-completion equivalence expressly identifies Koszul and quotient completion including their units, and the Koszul-reflector statement gives the Hom bijection and naturality. None of these is merely a definition of completeness being used as a preservation theorem.

Step 3 reads the coefficient map directly from the finite-projection clause of def-weil-pbc-completed-pullback. The same-index quotient map exists because e n is at least n. Both coefficient-square routes have the same finite projections, hence are equal by the limit property. The two displayed multiplication formulas are balanced and inverse to insertion of one. The tensor/pullback node states preservation of flat-term K-flat complexes; the monoidal-comparison node states associativity, composition and unit coherence for arbitrary structural ring maps. I deliberately did not apply lem-sfb-kflat-scalar-comparison-normalization: its coefficient rings on the source are required to be inverse images of the target coefficient rings, a stronger hypothesis unavailable here.

Step 4 uses the canonical adjunction clause of the ringed monoidal-comparison statement, not an unspecified choice of adjunction. For the ringed pushforward/completion statement the ideal is principal, and its generated image is exactly the source principal ideal since c sends the constant uniformizer to itself. Thus its preservation assertion and normalized isomorphism apply. The reflected-square statement has precisely the directions F1 CA to CB F0 and kappa inverse after Lambda(delta). With delta=beta inverse, inversion yields Lambda(beta) kappa in the required direction. The completed-pullback definition and constant-completion equivalence explicitly identify the quotient-tower functor and its specified unit; this does not replace the unit by an arbitrary object isomorphism.

Step 5 is elementary substitution from those unit equations and naturality of eta. I wrote every composite in its actual direction, including the intermediate Lambda(beta) eta expression. It proves equality of arrows, rather than merely existence of an isomorphism between their targets. Each quoted statement says the normalization it is used for.

Step 6 applies the constructible scalar-transport statement under the exact E subset L and scheme hypotheses of the item. It explicitly preserves the category with the same strata and compatible etale-origin witnesses. The realization/pullback node explicitly states that ordinary pullback preserves this category and that the specified gamma is an isomorphism. It applies once to K at E and once to CX K at L, on the same X and X'. No properness, smoothness or finite-type condition on g was inserted.

Step 7 uses the final pasting and identity sentences of the reflected-square statement, the coefficient-tower sentence of finite-free completion transport, and the identity/geometric composition/tensor-associator clauses of ringed monoidal comparisons. Their statements, not arguments hidden in their proofs, supply those laws. The raw associators in the item are the restrictions and rationalizations of these specified balanced associators. The universal reflection Hom bijections fix the completed comparison, so this proves its coherence for the actual units used in steps 4–5.

I checked B–E against the files and sources: there are no new-node form defects, no uncited non-elementary step, no citation of a definition for an unstated theorem, and no new node restating a clause. I checked dependency paths from the imported scalar-extension and the generic completion/monoidal/pullback tools: none reaches this item. The statement was not disputed or weakened. Small checks include the zero complex, empty scheme, identity geometric map, identity field extension with the chosen same uniformizer, and a ramified extension with e>1. The argument uses only principal generated ideals and positive powers, so these cases do not require excluding the zero object or supposing unramified coefficients. The proof stays on the unit's realization route.

Generic tools from other units are declared individually in split_report.tool_uses with their purpose: the curve-perverse unit does not prove ringed derived tensor/adjunction calculus or local-field scalar-completion transport. No maintainer-owned top-level tool_uses record is changed. No Lean, repository, launcher or literature file was written.

## Unfinished work

None in the mathematical split. The standalone server check_dag reported no finding introduced by this sandbox; review_split reported PASS with zero new nodes. The full deliver.py --no-push preflight passed at 8b49deb211d. This validation note is followed by a final dry run of the complete report and then direct delivery.
