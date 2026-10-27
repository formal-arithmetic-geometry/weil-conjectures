# Q89 stage-1 report

1. Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-dg-coefficient-module-comparison.json: item, split; unchanged statement and statement dependencies; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-ringed-dg-pushpull.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-finite-principal-hom-descent.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-compact-finite-cell-retract.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statements backing each step citation. Searches are preserved in searches.jsonl.

2. Attachments: none. Searched the project library both for the exact blueprint tag and for dgModule, DGModule, differential graded, and affine coefficient. The few hits concern ordinary complexes or a Koszul algebra, and none supplies this dg equivalence or all the coefficient comparisons. No compilation was run.

3. WANTED: none for this item. The inherited parent has a Kiehl request, but this comparison uses only the Stacks sources present here. No SGA source was used.

4. Initial faults and corrections: the item had no proof, and its source explicitly warns that the sheaf-dg comparison is an independent obligation. The statement itself is retained. In particular C_E -> T_E is not assumed to be a quasi-isomorphism. The ordinary affine equivalence alone does not transport a strict dg action. The new flat dg push-pull tool supplies an actual action-retaining derived adjunction; the ordinary equivalence then tests its unit and counit. Local perfectness is not simply declared global: finite principal-cover derived-Hom descent proves compactness first. The existing finite-cell compactness lemma only proves the opposite implication from the new compact-to-cell tool. An affine unit-ideal criterion encountered during the audit did not assert the principal-open basis and was removed before delivery; refinement is instead explained directly by the defining complements V(I). The null blueprint ancestor is inherited: tools/blueprint_refs.py ancestor prints None. The entire via chain is retained and each new node adds this item. Read the current latest blueprint chapter/unit and direct-image detailed statement and proof (3); this is a generic algebraic prerequisite inside the inherited descente route, with no chapter/unit change.

5. Unfinished: the three new nodes are deliberately statement-only obligations under the one-level split contract. Their statements are strictly more general tools than their uses here; none repeats an entire clause plus its coefficient hypotheses. No Mathlib leaves were found. Independent review and landing remain the maintainer's work.

## Review by Q89

I read Stacks perfect.tex, lemma-affine-compare-bounded (06Z0), including the unbounded unit/counit argument; sdga.tex, theorem-qis-into-dg-injective (0FT0), lemma-adjunction-push-pull-dg (0FRU), and lemma-derived-adjoint-push-pull (0FTR); dga.tex, proposition-compact (09R3), both implications; and perfect.tex, lemma-alternating-cech-complex-complex and lemma-alternating-cech-complex-complex-computes-cohomology (08D1/08D2). I also read the finite localization gluing argument algebra.tex lemma-cover-module (00EK). These sources do not directly state the combined coefficient comparison, so proof_origin is agent. For the new flat push-pull statement the source supplies dg injective resolutions and push-pull adjunction; the forgetful claim is justified because Hom_O(L,UI) = Hom_B(B tensor_O L,I), and B K-flat makes the right source acyclic whenever L is acyclic. For principal dg Hom descent, the extra obligation is dg Hom applied to the finite localization resolution of N: use a homotopically projective resolution of M and the localization adjunction, retaining the whole derived Hom isomorphism, not just its per-degree consequences. The new compact-to-cell statement is exactly the missing direction of 09R3, applied through the graded opposite for left modules.

Step 1 uses the coefficient definition for nonpositive flat terms and functorial augmentations, the bounded-flat K-flat lemma and stalk criterion for precisely the underlying complexes involved, and the tilde-sections and exact-localization statements for the exact termwise functor. Scalar extension of a flat D-module is S-flat by the displayed tensor identification even when S is not D-flat. Step 2 takes from the new flat dg push-pull node the actual adjunction and its underlying unit/counit comparison; 06Z0 supplies the ordinary equivalence for unbounded objects with QCoh cohomology. Cone vanishing is tested in the defining localization. This proves rather than assumes the dg equivalence, also over every S_f.

Step 3 takes finite principal-cover derived Hom descent from the new node, regular-module compactness from the existing finite-cell compactness node, and closure under finite triangles/retracts from compact-objects-thick. I included the existing dg triangulation and coproduct statements so those structures are supplied too. Quasi-compactness and the unit-ideal cover criterion are exactly clauses (iii) and (i) of the cited spectrum node. Principal refinement is a direct union-of-D(f) calculation. The finite Cech totalization is essential: sums commute with that finite construction; no exchange with an infinite totalization is used. Step 4 takes only the compact-to-finite-cell conclusion of the new 09R3 node, then writes the finite upper-bound argument out using nonpositivity. This does not claim boundedness below.

Step 5 uses the scalar adjunction node on a point, whose statement includes exactness, exact restriction and the action transpose. Restriction preserves coproducts on the unchanged complexes, so the proof shows ordinary extension compact. The existing ring-derived compact-perfect statement gives a genuine bounded finite-projective model over arbitrary T_E; the perfect-complex definition and affine equivalence give its scheme realization. Step 6 uses the existing relative bar statement with exactly its hypotheses: R_E and R_A are D-K-flat, while S and the input module need not be. The bar lemma explicitly fixes the counit on length zero and higher lengths, so it says exactly what is needed for normalization. The tensor/localization fraction formula identifies each term, face and degeneracy before passing to the derived category; the extension unit is the transpose under the same adjunction comparison.

Step 7 cites existence of unbounded K-injective replacements on the set-sized open sites, then the affine pushforward resolution lemma with the quasi-coherent terms of tilde K, without assuming the replacement quasi-coherent or bounded. The tilde-sections statement identifies both affine pushforwards with restriction term by term. Full faithfulness of the ordinary affine derived equivalence gives the assertion about every ordinary arrow. Step 8 uses the coefficient definition's explicit coefficient-linear composition comparison, not merely an isomorphism after forgetting E-actions, together with the bar lemma's actual action counit. Their composite is exactly the definition of nu_E. I read every cited node's statement; citations.json contains each exact statement, and proof_deps is the union of the uses lists.

Small cases checked: E=D gives C_D=S and recovers the ordinary affine equivalence. S=0 gives the empty scheme and the zero dg module category; choose a singleton principal cover with f=0=1 so the new descent tool's r>=1 applies. E=0 and A=0 likewise give zero regular dg objects. A one-open cover f_1=1 makes dg Hom descent the identity. C concentrated in degree zero recovers ordinary localization descent. The zero finite-cell filtration gives the zero object. Nonpositive C with infinitely many negative cohomology groups, taken as its own regular module, confirms that only an upper cohomological bound is asserted. With D=Z, S=F_p, E=F_p the augmentation can retain negative Tor; no step cancels it. Identity E->A and the length-zero multiplication counit recover the unit/counit identity. All eight non-elementary steps are below 2000 characters; none hides an additional independently named comparison. New obligations have no proof or proof dependencies, no proof sketch in their statements, and complete hypotheses.

The logged Mathlib searches include leanfinder, loogle, grep and leansearch for each new statement and a second semantic phrasing. I read the hits; ordinary pushforward/sheafification adjunctions, K-injective complexes, and derived fraction/t-structure lemmas do not state the dg claims. In particular I opened Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:34-51, Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:118-137, and AlgebraicGeometry/Modules/Sheaf.lean:189. Searches of all DAG chapters and tools/blueprint_refs.py searches for dg modules, dg pushforward, dg compact, dg Cech and compact differential graded found no duplicate tool. The existing ordinary affine/coherator, perfect-compact and Cech nodes were compared and reused where their statements apply; they cannot be cited for strict dg actions. Off-unit generic statements are declared in split_report.tool_uses rather than changing the unit route.

## Not duplicates
lem-sfb-flat-ringed-dg-pushpull vs lem-sfb-affine-dg-coefficient-module-comparison: general flat ringed-space dg push-pull and K-flat forgetful compatibility; does not state affine equivalence, perfectness or coefficient realization.

lem-sfb-flat-ringed-dg-pushpull vs lem-sfb-dg-coefficient-realization-comparison: the existing node compares a specified coefficient realization with an ordinary tensor and normalized arrow; it does not give general dg push-pull or the K-injective forgetful theorem.

lem-sfb-flat-ringed-dg-pushpull vs lem-sfb-ringed-dg-scalar-adjunction: the existing node is scalar change on one fixed site; the new node changes spaces and supplies compatibility of derived geometric pushforward with forgetting.

lem-sfb-flat-ringed-dg-pushpull vs lem-sfb-sheaf-dg-relative-flat-bar-extension: the existing node computes scalar extension by a relative bar; the new node is geometric derived push-pull and its underlying-complex comparison.

lem-sfb-dg-finite-principal-hom-descent vs def-sc-koszul-cech-comparison-construction: defines a particular ordinary Koszul-to-section cocone; the new node is arbitrary dg-module RHom descent.

lem-sfb-dg-finite-principal-hom-descent vs def-sc-principal-open-alternating-total: defines ordinary sheaf section Cech totals and the comparison; the new node is an isomorphism for derived dg-linear Hom.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-affine-koszul-cech-derived-comparison: ordinary Koszul-to-derived-sections comparison on a specified open; not arbitrary derived dg Hom.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-affine-koszul-hom-alternating-cech: ordinary Koszul Hom power-colimit isomorphism; does not state derived Hom over an arbitrary dg algebra.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-principal-cech-resolution-quasi-iso: ordinary sheaf-complex resolution comparison; does not construct dg Hom descent.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-principal-open-sections-resolution-quasi-iso: compares ordinary basic-open sections with a K-injective replacement; no dg-linear RHom assertion.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-principal-open-sections-restriction-comparison: equivalence of two ordinary quasi-isomorphism tests; no dg Hom descent or Cech reconstruction.

lem-sfb-dg-finite-principal-hom-descent vs lem-sc-qcoh-complex-alternating-cech-derived-sections: ordinary quasi-coherent sheaf-complex sections and RGamma; no dg-linear Hom or localization adjunction for arbitrary dg modules.

lem-sfb-dg-compact-finite-cell-retract vs lem-sfb-affine-dg-coefficient-module-comparison: general compact-to-finite-cell implication with no affine sheaf data; the item must first prove affine equivalence and compactness and then compare coefficients.

lem-sfb-dg-compact-finite-cell-retract vs lem-sfb-affine-perfect-dg-finite-stage-descent: descends an already finite-cell-retract perfect object through coefficient stages; does not derive a finite-cell retract from compactness.

lem-sfb-dg-compact-finite-cell-retract vs lem-sfb-dg-finite-cell-compact: opposite implication, finite-cell implies compact; it does not supply a finite-cell retract from an arbitrary compact object.

