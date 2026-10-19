# pur9-def-exact-transformation — stage 1, NU

## Files written

- `dag/nodes/sec-smooth-purity/pur9-def-exact-transformation.json`: definition; Mathlib leaf `CategoryTheory.NatTrans.CommShiftCore`, specialized to degree one. The natural-language statement is unchanged; `stmt_deps` now names `def-weil-triangulated-category`.
- `citations.json`: empty list, since a definition/Mathlib leaf has no proof steps.
- `report.md`: this report. No new nodes; one Mathlib leaf (the item).

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint id, the phrase “morphism of exact functors”, and declaration names involving exact transformations. The general predicate is a Mathlib declaration, not a project declaration; the project has examples and preservation lemmas for CommShift, which do not define this item.

## WANTED

None. The current blueprint and pinned Mathlib source were both available locally.

## Findings and changes

The imported statement is correct and was preserved verbatim. The missing statement dependency is the existing definition of triangulated categories and exact functors. The prior empty Mathlib search list missed a direct leaf. Seven actual search queries are recorded from `searches.jsonl`, including the unsuccessful unqualified Loogle identifier and the successful fully qualified retry. The single-file grep wrapper displayed malformed file/line fields; the original source was opened with numbered lines and confirms 286–288 and 301–304.

I read the chapter and unit records and the current main-20261015 definition and unit text. The generic definition does not replace any localization argument and requires no unit-realization edit. The older unit record differs from the current blueprint in its localization setting; that does not affect this definition. No coefficient categories, base-change morphisms or targets changed.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for “morphism of exact”, “exact functors”, and `CommShiftCore` found the item and applications, but no other blueprint definition of the same object. `lem-weil-pbc-commshift-nattrans-comp-whisker` includes the square in its hypotheses but states stability under composition and whiskering; it is not another definition node. `lem-sf-triangle-two-out-of-three` uses the square to prove isomorphism propagation; it is also a distinct statement. Accordingly `blueprint.same_as` is empty.

## Review by NU

I checked B–E against the source rather than inferring the notion from a name. For the item, I read `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/pur9-def-exact-transformation.md` and `Mathlib/CategoryTheory/Shift/CommShift.lean` lines 275–304. The blueprint asks for exactly one square, at shift [1]. Mathlib’s `CommShiftCore α (1 : ℤ)` has exactly that square as its sole field. Evaluating the field at X gives `sΦ_X ≫ α_X[1] = α_{X[1]} ≫ sΨ_X`; reversing the equation and the composition notation gives the displayed blueprint equation. Conversely the component equations imply the natural-transformation equality by extensionality. This is definitional agreement, not a separate comparison theorem. Using the fixed-degree Core predicate avoids silently strengthening the condition to every shift.

I read the statement of `def-weil-triangulated-category`: it defines both the triangulated categories and the exact functors with their shift isomorphisms. Its recorded Mathlib interface is `[HasShift C ℤ]`, `[F.CommShift ℤ]`, and `[F.IsTriangulated]`; thus the given exact-functor data supplies the ambient parameters of Core. Exactness is only an ambient assumption; the square imposes no additional exactness hypothesis on α and does not require α to be invertible. In particular this is not a natural-isomorphism-only predicate. Core works in a more general ambient category, which specializes directly here.

For small cases, the identity transformation makes both sides equal to the same shift isomorphism; the zero transformation between additive exact functors makes both sides zero. A nonzero scalar endomorphism for identity functors with equal shift structures obeys the same equation, confirming that invertibility is not required. If the two shift isomorphisms differ, the identity underlying transformation need not qualify, just as the blueprint square says. Both composites have source Φ(X[1]) and target Ψ(X)[1], so no type mismatch or sign change is hidden.

There are no proof steps, no step citations, no new statements needing edge-case repairs, and no long steps hiding lemmas. No new-node source/tag pairs require duplicate justifications. Existing metadata and import flags were retained. The only corrections were the missing statement dependency, the previously absent search records/leaf match, and the unsearched `same_as` field. I did not use the proof of another node as a theorem or cite any prohibited source.

## Unfinished work

None in the stage-1 mathematical task. The required server dry run and delivery follow this report.
