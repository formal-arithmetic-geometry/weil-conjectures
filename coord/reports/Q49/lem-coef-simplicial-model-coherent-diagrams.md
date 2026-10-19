# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-model-coherent-diagrams.json`: repaired item proof; statement and Lean record unchanged.
- `dag/nodes/sec-six-functors/lem-coef-bifibrant-comparison-common-replacement.json`: new statement-only supporting lemma; Mathlib searches found no exact match.
- `dag/nodes/sec-six-functors/lem-coef-fibrant-pullback-mapping-invariance.json`: new statement-only supporting lemma; Mathlib searches found no exact match.
- `citations.json`: regenerated verbatim statement quotes for every step citation.

## Attachments

None. The existing declaration in `lean/Sheaf/CategoryTheory/SimplicialModelCoherentDiagrams.lean` is the stage-2 target with a `sorry`, so it is not an attachment.

## WANTED

- `https://www.math.ias.edu/~lurie/papers/HTT.pdf`, Appendix A.1.2, A.2.4, A.2.8, A.3.3 and Chapter 4.2.4, for the item and both new supporting nodes. The online Harvard copy was read; it is not archived under `literature/`.

## Not duplicates

- `lem-coef-bifibrant-comparison-common-replacement` vs `lem-coef-enriched-diagram-rectification`: the existing node states rectification for the projective presentation, while the new node states the comparison of projective and injective bifibrant presentations through a common localization and a replacement functor.
- `lem-coef-fibrant-pullback-mapping-invariance` vs `lem-coef-kan-homotopy-pullback-invariance`: the existing node compares homotopy pullback spaces in Kan complexes, while the new node proves mapping-space invariance for a strict pullback in a simplicial model category under the all-cofibrant and fibrant hypotheses.

## What was wrong and what changed

The return identified Steps 2, 5 and 10 as non-elementary long steps. I kept the item's statement, route, source and Lean record unchanged. Step 2 is now a short application of the existing projective-model theorem together with the existing cellular factorization, lifting-closure and transfinite-lifting statements; it no longer reproves all model recognition details inline. Step 5 now cites `lem-coef-bifibrant-comparison-common-replacement` for the substantial common-localization/replacement argument, while retaining the existing enriched-rectification, nerve-localization and cone-calculus citations. Step 10 now cites `lem-coef-fibrant-pullback-mapping-invariance` for the substantial fibrant pullback mapping argument. The endpoint homotopy and relative cone identification formerly hidden in Step 10 are a new Step 11, citing the existing mapping-composition, contractible-fiber and cone-calculus statements. Every proof step is below 2000 characters. I restored and retained the maintenance-requested Smith recognition, accessible weak-equivalence, enriched rectification and nerve-localization citations. A read-only closure audit found 488 nodes, no cycles and no missing references.

## Review by Q49

I read the current item node, its stage-2 Lean declaration and docstring in `WeilConjectures/SixFunctors/CategoryTheory/SimplicialModelCoherentDiagrams.lean` from the read-only slopmaster2 checkout, the `sk-prop-sf-biduality-general` unit, and the current main-20261015 blueprint proof paragraph. The item statement is unchanged and agrees with the HTT route: combinatorial simplicial model category, strict enriched projective/injective diagram models, coherent rectification, enriched cone/cocone adjunctions, and the all-cofibrant fibrant-cospan path-object clause.

For Step 1 I checked `lem-coef-enriched-diagram-size-generation` for locally presentable enriched diagram categories and free evaluation, and `lem-coef-kan-quillen-right-proper` for the Kan cofibration from the initial simplicial set and the pushout-product consequence. Step 2 now uses the existing `lem-coef-simplicial-projective-model-calculus` statement for the projective model structure and objectwise weak equivalences/fibrations, `lem-coef-presentable-cellular-factorization` for cellular factorizations, `lem-coef-lifting-class-closure` for pushouts/retracts and `lem-coef-transfinite-left-lifting` for limit stages. The hypotheses are the given combinatorial and simplicial model assumptions; no objectwise cofibration equality is asserted.

For Step 3 I opened `lem-coef-enriched-diagram-size-generation`, `lem-coef-model-weak-equivalences-accessible` and `lem-coef-smith-model-recognition`. They say exactly the pointwise generation/accessibility, accessible arrow subcategory of weak equivalences, and five Smith-recognition hypotheses used there. Step 4 is elementary: it expands the pushout-product on free diagrams and closes under the cellular operations already cited in Steps 1–3.

For Step 5 I read `lem-coef-enriched-diagram-rectification`, `lem-coef-simplicial-model-nerve-localization`, `lem-cbc-enhanced-functor-cone-calculus`, and the new common-replacement statement. The first gives the projective rectification comparison; the second gives coherent localization by bifibrants, mapping spaces and universal functor restriction; the third gives the vertexwise equivalence criterion; and the new statement records the common localization, functorial projective replacement, and the resulting natural equivalence of projective and injective comparisons. The injective objectwise fibrancy check uses the free-evaluation test from Step 1. Steps 6–8 use the existing enriched-diagram-size-generation and cone-calculus statements: the coequalizer/end formulas are direct enriched adjunction calculations, and the cited cone criterion says exactly that the displayed mapping-space equivalences identify the canonical cocone and cone as limiting.

For Step 9 I checked the fibrant cospan construction against HTT A.2.4.4 and Remark A.2.4.5. The maps from the path object to the fibrant base are fibrations, the sections are weak equivalences, the replacement cospan is injectively fibrant, and its strict limit computes the coherent pullback by the already established diagram comparison. Step 10 now uses the new `lem-coef-fibrant-pullback-mapping-invariance` statement, whose hypotheses match the final all-cofibrant clause: fibrant source and target, a weak equivalence, and a fibration. Step 11 uses `lem-coef-infinity-mapping-composition` for coherent composition and inverse homotopies, `lem-coef-space-contractible-fiber-equivalence` for the contractible homotopy fiber over the identity, and `lem-cbc-enhanced-functor-cone-calculus` for transfer of the limiting cone along an apex equivalence. This explicitly supplies the relative endpoint homotopy and cone compatibility that had been hidden in the returned long step.

I tested the statement route on the empty index, a point, a discrete cospan, identity legs, and the simplicial-set path-object case. The new pullback lemma reduces in the simplicial-set case to the usual mapping-space pullback argument and does not assume model-category right properness. I also ran the required Mathlib searches recorded in each new node; the LeanSearch service was unavailable for the two final extra queries and is recorded as unavailable in the search log, while LeanFinder, Loogle and source grep were run and read. No Lean source was written and no compiler, Lake or build command was run.
