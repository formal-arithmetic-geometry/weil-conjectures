# Stage-1 report: def-pur-completed-scalar-shift-coordinates

## Files written

- dag/nodes/sec-smooth-purity/def-pur-completed-scalar-shift-coordinates.json — definition, split; not a Mathlib leaf. The four maps/predicates remain the same definitions. Their ambient objects, coherent shift convention and component equations are now explicit, and their statement dependencies are audited.
- citations.json — empty list, since this definition has no proof steps or proof citations.
- report.md — this report.

There are zero new nodes and zero Mathlib leaves. The sandbox initially contained no node, split or report; I copied the live item and retained its pre-existing search records, blueprint ownership and Lean record. I have not written Lean, run a compiler, changed the repository, or changed launcher files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, the four declaration names and completed-scalar/shift concepts. There is no upstream declaration stating this item. The four existing declarations in lean/Sheaf/Paper/CompletedScalarShiftCoordinates.lean are reference material for its intended definitions, not an attachment under the worker's upstream-only rule.

## WANTED

None. The cited Stacks sources and current blueprint are present locally.

## Corrections and scope

The live node was marked split but had no split_report or reviewed entry. No released repair order exists for this id. Its statement attributed coherent integer comparisons and the localization comparison to def-weil-triangulated-category, whose actual statement gives triangulated-category axioms and the single-shift exact-functor interface. That citation does not supply the claimed localization interface. I instead cite def-weil-abstract-derived-category for Q and its shifts, write the meaning of a coherent integer shift structure explicitly, and cite lem-weil-integral-scalar-extension-well-defined for the retained comparisons on K-flat representatives. This is a clarification of the existing four definitions, with no added existence theorem.

The previous citation to lem-weil-finite-free-completed-scalar-comparison supplied no necessary extra datum: the actual endomorphism 1-s is already determined by the quotient transitions in def-weil-integral-scalar-extension. I replaced it with def-weil-tower-transition-endomorphism and specified its projection equations. In particular no derived-completeness hypothesis on an arbitrary cochain complex P is needed or imported. I cite def-weil-signed-mapping-cocone-functor for the cocone convention and spell out both inclusion equations with their degree reindexing; the degree-zero inclusion is not mislabeled a chain map.

No imported statement is false and there is no STATEMENT-DISPUTED. No unit or chapter statement or route is changed. The item is a supporting definition for the Weil-structures paragraph of the current all-stages open-closed triangle, not the key node of the unit; no unit realization file is edited.

## Search results and reuse

Searched the full DAG for the four exact completedScalarShift names, scalar-shift keywords, CommShift and the signed-cocone interface, and ran blueprint_refs.py ancestor and searches for "completed scalar shift", "scalar shift" and "signed mapping cocone". The current item owns the four definitions; lem-weil-point-completed-scalar-shift is their consumer and a theorem asserting compatibility, and lem-weil-completed-scalar-chain-shift asserts existence of the coherent chain shift. Neither is a replacement definition or an attachment. The existing general cocone and localization nodes were reused. No new node is needed.

All fresh Mathlib searches used msearch.py and are recorded verbatim in searches.jsonl and mathlib_searches. LeanSearch and both concept phrasings of LeanFinder returned general shifts, cochains, localization or unrelated cocones, with no completed-scalar normalization predicate. The first Loogle pattern used an unqualified identifier, which Loogle rejected as unknown; the recorded diagnostic is not evidence of mathematical absence. I then searched the quoted declaration substring, found CategoryTheory.Functor.mapCochainComplexShiftIso and read Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean:247-275: the comparison has identity degree components. The quoted PreservesProduct.iso query found the generic product-preservation comparison. Those are ingredients, not the whole definition with its specific scalar tower and normalization predicates. The exact completedScalarShift/normalization grep had no Mathlib hits; the broader grep found the additive comparisons. The MappingCone-only grep naturally missed the cocone definition; the follow-up homology-wide grep located MappingCocone.lean, whose definitions at lines 33, 51 and 55 I read. These results support retaining a project definition node rather than labeling the whole item a Mathlib leaf.

## Not duplicates

No new nodes. def-fd-integral-pullback-shift-coordinates concerns the finite pullback tower associated to a scheme morphism, whereas this item concerns quotient scalar extension along a coefficient-field embedding. def-weil-signed-mapping-cocone-functor is the generic signed cocone interface, which this item reuses; it does not define the scalar finite-level/product maps or the retained derived normalization predicate. The two scalar-shift theorem nodes cited above assert compatibility; this item only defines the predicates used to state compatibility.

## Review by O3

I read the item, its chapter and unit records, the current blueprint's all-stages open-closed-triangle proof, all six dependency statements, and all four existing Sheaf definition bodies. For source conventions I read Stacks homology.tex Tag 011G (definition-shift-cochain), derived.tex Tags 014E (definition-cone) and 08TC (definition-derived-limit), and sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 06YT (lemma-derived-tor-quasi-isomorphism-other-side) and 06YU (definition-derived-tor). The blueprint's Weil-structures paragraph motivates compatibility, but does not itself supply these auxiliary formulas; the formulas are explicitly the definitions already present in the Sheaf interface, with Stacks fixing their conventions. No source is being cited as an omitted proof.

This is a definition, so there are no proof steps to audit under C1/C4 and no step quotes to put in citations.json. I audited each defining clause instead. The first clause uses def-weil-integral-scalar-extension's explicit finite coefficient rings, restricted scalar complexes and actual transitions. The tower-transition definition supplies exactly the projection characterization of 1-s. The K-flat qualification comes from def-pur-integral-derived-operations, without requiring completeness or boundedness. The retained comparison is supplied by the well-definedness node's clause 2, which explicitly specifies natural comparison isomorphisms on K-flat representatives and independence compatible with them. None is taken from a dependency's proof alone.

For the level and product maps I checked the two successive additive comparisons in the actual completedScalarShiftLevelIso body, and the product of those maps followed by inverse PreservesProduct.iso in completedScalarShiftProductIso. The identity after reindexing and projection characterization give concrete maps and inverses; there is no existential choice of product or tower map and no new compatibility theorem hidden here. For the cone predicate I compared the two displayed component equations to completedScalarShiftConeFormula, including the separate quantifier i+1=j and the inverse degree reindexing. The cited cocone interface supplies the shifted-cone object; the two equations are a predicate on a given e_C and assert no existence or chain-map theorem.

For the integral predicate I checked the order of all four factors against completedScalarShiftIntegralNormalization. Both composites start at T((QP)[m]) and end at (QC(P))[m]: T(eta^{-1}) precedes d_{P[m]}, Q(e_C) precedes eta_{C(P)}, and the other side is e_T followed by d_P[m]. The witness that P[m] is good is part of the predicate, just as the existing existential proof witness is; it is not silently proved by citing the definition of K-flatness. No independent coefficient or geometric universe equality, flatness of a scalar functor, or derived-completeness assumption is introduced.

I tested zero and negative shifts, the first quotient n=0 (exponent one), the zero complex and E=L. At m=0 both signs are one and the two normalization sides have the unshifted comparison as type; for odd negative m the second coefficient remains minus one, while for even m it is one. At n=0 there is no zero-th power quotient or missing predecessor transition. For the zero complex all components are zero maps; for E=L the same specified quotient tower is used rather than falsely replacing the Roos functor on all complexes by the identity. These tests introduce no theorem asserting that an arbitrary pair e_C,e_T satisfies the predicates. Every statement-dependency id names precisely the notion or comparison used; the removed finite-free theorem was not used. There are no proof steps longer than 2000 characters, and no auxiliary claim moved into a new node. This completes the B–E checks without new unsplit leaves or source errors.

## Unfinished work

None in the stage-1 definition split. Existence, coherence and descent assertions about the defined predicates remain the work of the existing theorem nodes and are deliberately not asserted here. Delivery is subject to the required remote dry run and independent maintainer review.
