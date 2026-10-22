
## cor-amb-affine-space-adjunction (2026-10-14 09:34 UTC, branch head 0f9e0bc307)

C4/E5/E6: the new P1 prerequisite omits the source’s specified trace counit and diagonal unit; its unspecified adjunction cannot support unchanged downstream normalization and base-change claims. Repaired the missing projective-space interface citation under fixes. Both new nodes also omit required metadata. Full checks and source locations are recorded in review.md.

## lem-pc-ringed-space-product-kinjective (2026-10-15 10:03 UTC, branch head 192c0643b5)

L: independent stage-2 immutable head 192c0643b5fa: H4 duplicate: existing sorry-free CochainComplex.termwise_product_isKInjective_and_isLimit compiles from KInjectiveProducts.lean; attach it instead of delivering _stage2.

## thm-sf-fullcd-class (2026-10-15 20:21 UTC, branch head 91e620b11f)

L: the delivery could not be prepared for review:  Repair what this says (the report needs the sections the brief lists) and push again.

## lem-cbc-extension-zero-projection-formula (2026-10-15 21:56 UTC, branch head f81014856a)

L: independent stage-2 immutable head f81014856a32: H3/H4: supply canonical transport to the recorded SheafOfModules derived tensor and record the actual pro-etale extension-by-zero dependency. Specialization compiled cleanly; branch unchanged.



## def-pur-roots-of-unity-inverse-image (2026-10-16 04:53 UTC, branch head f4fd7b1c8d)

L (re-issued by the launcher; the entry had been lost): NV lem-pur-diagonal-base-change --stage 1 --reviewer NT-Codex-NV-f8a59d860 --head f8a59d8604526f9c5a5d7295b89c5c18a6d85184 --spot-checked Read the complete item, unit/chapter route, every cited node, exact blueprint source, and cited Stacks locations. All five proof steps are valid with correct hypotheses, morphism orientations, coefficient category, and edge cases; citations and proof_deps agree, no circularity or duplicate/new-node issue exists, and no attachment is justified. --verdict PASS


## def-weil-point-finite-cohomology-complexes (2026-10-16 04:53 UTC, branch head b43357d60e)

L (re-issued by the launcher; the entry had been lost): l-boundary-duality-discharge --stage 1 --reviewer NT-Codex-Q24-cce734ae2 --head cce734ae2a4ac74c46dd5d293584c51d50d32b0d --spot-checked Read the full item, report, all 36 cited statements and source places, and unit/chapter route. Verified all nine steps, evaluation-normalized beta, double-dual compatibility, revised comparison hypotheses, edge cases, and absence of cycles or duplicates. Accepted all 25 declared tool uses. No repairs needed; concrete checks recorded in review.md. --verdict PASS


## lem-exc-dvr-galois (2026-10-16 04:53 UTC, branch head fb7583d2e6)

L (re-issued by the launcher; the entry had been lost): NT-Codex-NI-dbb05f32e --head dbb05f32eaa6e58f595028d584ab86a8bd44d934 --spot-checked Read the complete item, cited statements, master sources, report, and unit/chapter route. All four steps, associator directions, inverse calculations, edge cases, and dependency checks pass. Accepted lem-fix-operation-reduction as the declared comparison tool. No new nodes or repairs. Condensed-category and exchange-map comparisons remain separate target obligations; review.md records the checks. --verdict PASS


## lem-exc-finite-type-localization-excellent (2026-10-16 04:53 UTC, branch head 2b60944753)

L (re-issued by the launcher; the entry had been lost): The mathematics and citations were read and are largely sound, but the item is assigned to unit sk-prop-a1-kummer, whose statement and steps concern étale Kummer cohomology of A¹ and Gₘ. This delivery instead proves a sentence from lem-exc-punctured-curve-branches using a separate commutative-algebra route, without an established unit error authorizing departure. Return under delivery-error C7 and the stage-1 unit-route rule for reassignment or documented route correction.

## lem-weil-compact-support-reduction-tower-functor (2026-10-16 08:26 UTC, branch head 8b1bc4e627)

L: the delivery could not be prepared for review: NOT MERGED lem-weil-compact-support-reduction-tower-functor: the report lacks the heading '## Review by NB' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## sbc-def-admissible-lattices (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
B3 (exact statement dependencies): def-weil-pbc-witness-compatibility is extraneous in stmt_deps. The definition requires only membership in the finite-level essential images, explicitly without chosen witnesses or compatible witness towers; no WIT predicate or compatible witness data of that dependency is used. Remove this edge, retaining the existing essential-image condition unchanged.

## lem-weil-pbc-strict-tower-exchange-mate-normalization (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 5 (2096 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 5 (2096 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-point-fibre-equivalence (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 11 (3147 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 11 (3147 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## sk-lem-proper-unbounded-window-ii (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2897 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2897 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-cbc-proper-support-fibre-restriction-compatibility (2026-10-17 20:35 UTC, branch head 1f6ccbdac8)

L: independent stage-2 immutable head 1f6ccbdac859: stage-2 checks: (c) --drop-files lean/Sheaf/SecSmoothPurity/ProperSupportFibreRestrictionCompatibility.lean: not a new module lean/Sheaf/<...>.lean of this delivery | (d) lean.existing is true but the commit has Lean file(s) lean/Sheaf/SecSmoothPurity/ProperSupportFibreRestrictionCompatibility.lean | (c) lean/Sheaf/SecSmoothPurity/ProperSupportFibreRestrictionCompatibility.lean: no node of the delivery has it as lean.file (every module is the module of the item, of a new definition node or of a dependency node)

## sk-def-sfb-bounded-constructible (2026-10-18 02:10 UTC, branch head cfd6713a8f)

L: independent stage-2 immutable head cfd6713a8ff9: H3/H13: the bound AlgebraicGeometry.ProEtale.IsConstructibleModuleObject (published ProEtaleModule.Def, used by boundedConstructible) quantifies over Scheme.Stratification, which extends Topology.Stratification with isConstructible_stratum. The item and def-sfb-constructible-module only require a finite stratification [def-constructible-stratification] by locally closed strata; that node's side record explicitly drops constructibility ('the consumer adds constructibility explicitly'). On non-Noetherian X the Lean is strictly stronger: the skyscraper at a non-isolated closed point of Spec prod F2 is node-constructible but not Lean-constructible. The report's claim of exactness is wrong, and the §1(B) rebinding of def-sfb-constructible-module does not state that node's notion. Re-deliver either (a) a dependency module over Scheme.FiniteLocallyClosedStratification plus an item module on it (triangulated theorem with the five hypotheses, sorry), or (b) a source-based §1(C) statement_change of the item adding constructible strata (sk-def-sfb-constructible item 2, BS 6.8) with citer audit, citing def-constructible-stratification and def-sfb-locally-finitely-presented (bind it to the existing IsLocallyFinitelyPresented) and dropping the def-sfb-constructible-module rebinding. Everything else checks out: same sheaf tensor (Sheaf.monoidalCategory), Mathlib MonObj/Mod/DerivedCategory/t.bounded/IsTriangulated, verbatim statements, universes, a<=b via min/max, ambient morphisms (fully faithful iota), no completeness, five-hypothesis triangulatedness from the live isTriangulated_boundedConstructible_of_serre. Reproduced nt_compile check: rc=0, no warnings, axioms propext/choice/Quot.sound only.

## lem-trf-restricted-quotient-complete (2026-10-19 04:00 UTC, branch head 57f1f9e2b4)

L: approved by the reader, but the landing refused it: NOT MERGED lem-trf-restricted-quotient-complete: lem-trf-restricted-quotient-complete: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-pbc-projection-mate-square-coherence (2026-10-21 10:04 UTC, branch head e821de19b9d)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-projection-mate-square-coherence: lem-weil-pbc-projection-mate-square-coherence: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-ramified-cartier-supported-purity (2026-10-22 03:09 UTC, branch head 63024491b62)

I read all eight steps. The item is live: it was created 2026-10-22 by NV for its live citer lem-sfb-root-coordinate-supported-vanishing, and neither is on the drop list. The fault is in the cited nodes. Three of them are in the 2026-10-19 artin-gabber section of clones/side-live/coord/route-pivot-dropped.txt: lem-per-gabber-regular-pair-purity (line 1608, Step 3), lem-per-regular-immersion-class-calculus (line 1869, Step 3) and lem-per-noetherian-supported-product-calculus (line 1738, Step 6). E1, not repairable by re-citing: the item says P_D and P_D' are isomorphisms for arbitrary Noetherian regular affine X, X' with regular divisors. That is codimension-one absolute (Gabber) purity, ILO XVI 3.1.1. No live node gives it. The live purity nodes thm-pur-regular-immersion-purity and sk-thm-regular need X smooth over a perfect field, and lem-pur-gysin-structure covers only the zero section of A^1_Y. Every node stating purity on general regular schemes is dropped (gabber-regular-pair-purity, per-absolute-gysin-purity at line 1387, regular-constant-gysin-potential at line 1864). Fixing this would weaken the target, which is not allowed. On top of that, Step 3's class-calculus cite (codimension-one transpose and positive O(D) sign) and Step 6's supported Chern additivity cite are dropped too and would need re-citing. Batch 5: the three trf nodes reached (bounded-below-derived-adjunction, def-trf-fs-log-blowup, oriented-closed-base-localization) are generic and not steps of the trace formula or Poincaré duality, but they are reached only through the dropped nodes. The rest of the mathematics is sound. Step 1: E=V(g^e) has the same support as D', and the reduction unit is an isomorphism. Steps 2 and 7: the lift is unique because Hom into Rj_* of an object supported on the divisor vanishes. Step 5: (g)^{⊗e}≅(g^e) with its trivialization. Step 6: c_E = e·c_D'∘α. Edge cases checked: D empty forces D' empty; D' empty; e=1; ℓ^s|e gives zero. Remedy: restate the item in the generality the citer actually needs, for example a smooth-over-perfect-field or root-tower limit setting that uses thm-pur-regular-immersion-purity. That is for the citer's owner or the maintainer. No fixes were written.
