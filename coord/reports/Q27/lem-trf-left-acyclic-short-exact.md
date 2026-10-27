# Stage-1 delivery: lem-trf-left-acyclic-short-exact

## Files written

- dag/nodes/sec-trace-formula/lem-trf-left-acyclic-short-exact.json — statement, split into six steps; no exact project attachment or Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-left-derived-object-cohomology.json — one new statement-only node, unsplit. Mathlib has classical resolution-based degree-zero normalization, but not the full claim for the total pointwise-derived counit.
- citations.json — nine entries, covering every cited node in every proof step with verbatim statement excerpts.

## Attachments

None. Searches for the item's blueprint tag, left-acyclic terminology, and leftDerivedZero in lean/WeilConjectures found no declaration giving both clauses. No sorry declaration was treated as a proof. Mathlib's Functor.leftDerivedZeroIsoSelf is a candidate for part of the new node, not an attachment.

## WANTED

None. All sources used are present in literature/stacks-project/derived.tex and its tag table.

## Corrections and scope

The imported statement is correct and is unchanged. Its empty proof is replaced by the dual of the proof of Tag 015D, lemma-F-acyclic-ses, rather than by two nodes restating its conclusions. The new node concerns one object and the canonical total-derived counit; it asserts no closure or short-exact-sequence result. Enough projectives and everywhere-definedness are retained. In particular, enough projectives alone is not claimed to give unbounded derived existence.

The total-derived object-cohomology input includes positive cohomology vanishing and degree-zero normalization. Neither can be read off merely from the definition of an abstract Kan extension. They have therefore been exposed as one genuine supporting node instead of being hidden in an elementary step. The final acyclicity criterion is included with that input, rather than creating an additional elementary corollary node.

Existing generic nodes supply the single-complex short-exact triangle, exactness of LV, saturation and localization exactness, and the cohomology long exact sequence. Their off-unit uses are declared in split_report.tool_uses. The pre-existing blueprint ancestor, via chain, chapter, and unit are preserved; this is the object-level homological input underneath the existing bounded-above computation node. No chapter or unit statement or route is changed, and no SGA source is used.

## What could not be finished

No part of this one-level split remains unfinished. The new object-cohomology input is deliberately statement-only, as required for a new unsplit node. Its eventual proof must compare the total-derived value with the bounded-above theory, not silently identify classical Mathlib leftDerived with that total value.

## Review by Q27

I read derived.tex at lemma-F-acyclic-ses (015D), lemma-F-acyclic (015C), lemma-negative-vanishing (05TC), lemma-left-exact-higher-derived (05TD), and lemma-irrelevant (05T5). The source's right-derived proof uses higher vanishing and the long exact sequence. Dualizing reverses the short exact sequence and changes the higher-derived cohomological indices to negative integers: the source's second clause becomes the item's kernel-of-an-epimorphism clause, not a cokernel clause. I checked this against the actual index segments in steps 5 and 6.

For the new node I read those same source lemmas: 05T5 (3) and (4) explicitly handle the unbounded/bounded-above comparison at M[0], while the duals of 05TC and 05TD give positive-degree vanishing and the degree-zero counit isomorphism. The dual of 015C characterizes invertibility of the actual comparison by negative-degree vanishing. The statement defines its categories, projectivity hypothesis, right exactness, denominator diagram, comparison, single complex, and T^q. Naturality is stated as the equation c_N T^0(f) = V(f) c_M; thus it identifies the maps needed by the item, not merely the objects. Its proof is not embedded in its statement.

Step 1 uses precisely these three conclusions of the new node. I verified that the item's hypotheses supply every hypothesis, including enough projectives and pointwise derivation on unbounded complexes. The degree-zero map is H^0 of the same counit as in the item.

Step 2 was checked against the full statements of lem-trf-additive-homotopy-category-triangulated and lem-pur-quasi-isos-saturated-triangulated, and against 014X in derived.tex. The first node supplies the homotopy equation, signed shift, cone matrix and cone triangulation. The step actually applies V to each entry of these equations and the finite-biproduct comparison to the cone; it does not cite that node for an unstated functor theorem. The second node explicitly supplies the saturated triangulated multiplicative system and exactness of Q. Additivity and finite direct sums are enough here; exactness of V on all short exact sequences is never assumed.

Step 3 uses lem-sf-derived-ses-triangle for the distinguished triangle of the GIVEN short exact sequence, and lem-pur-left-derived-exact-when-defined for exactness of LV. I opened both statements: the former has arbitrary abelian categories and single complexes, and the latter requires an exact source functor, saturation, compatible triangulation, and everywhere-definedness, all supplied in step 2 and the item. Neither statement requires V to be an exact abelian functor. The named arrows i and p remain the first two arrows of the derived triangle.

Step 4 uses the full statement of lem-sf-derived-homology-long-exact, not just a definition of homological functor. It gives exact consecutive cohomology terms in every integer degree. The new node's explicit naturality equation conjugates T^0(i) and T^0(p) to exactly V(i) and V(p). The displayed degree-zero tail ends at zero because T^1(M')=0. Thus the short exact image is the one specified in the item, with no unproved compatibility of arbitrary choices of identifications.

In step 5 the outside terms T^q(M') and T^q(M'') are zero for q<0; exactness gives T^q(M)=0. In step 6 the outside terms are instead T^{q-1}(M'') and T^q(M), both in negative degrees. The q=-1 case is included: it uses T^{-2}(M''), so there is no missing boundary case. In both cases T^{-1}(M'')=0 makes V(i) monic in the already established exact tail, and V(p) is epic. Each final step cites the new node only for the acyclicity criterion; the vanishing deduction itself is elementary exactness at a zero-flanked object. No non-elementary subclaim is hidden in these final steps.

I tested zero objects, the identity functor, the zero functor, and split exact sequences; the claims give the expected results without nonzero-object assumptions. For a nonexact right exact functor I used tensoring abelian groups with Z/2: the sequence 0 -> Z -> Z -> Z/2 -> 0 does not falsely satisfy clause (2), because the quotient has nonzero negative derived cohomology. This also checks why acyclicity of the quotient is indispensable to the proof of image injectivity. For the new node this test gives H^0 = tensor and possible H^{-1}, with no positive cohomology, matching its indexing and comparison direction.

I checked B1--B10: the new node is self-contained and statement-only, TeX is singly escaped in the decoded text, its source uses the actual tag-label pairs, every notion is inline or attached to its definition, and the blueprint search found no matching imported node. Mathlib searches were made only with msearch.py and read as returned, including a second semantic phrasing for each search question. Mathlib/CategoryTheory/Abelian/LeftDerived.lean:302-313, 341-367 and CategoryTheory/Functor/Derived/LeftDerived.lean:45-58 distinguish the classical resolution functor from the total counit, so the new node is not falsely marked a Mathlib leaf. I checked C1--C8 with the cited statements open and wrote the verbatim citation manifest. The proof has no appeal to the parent's bounded-above acyclic computation, which depends on this item, so it introduces no such cycle. D1--D5 are addressed by keeping the two closure arguments in the item. E1--E7 are addressed by the hypothesis, index, map, and small-case checks above. Every proof step is below 2000 characters.

## Not duplicates

lem-trf-left-derived-object-cohomology vs lem-dl-a1-weil-open-image-delta: the existing statement concerns Low-degree open direct-image sequence for adic Weil sheaves; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-per-proper-finite-coefficient-bounded-preservation: the existing statement concerns Proper direct image preserves ordinary finite-coefficient bounded constructibility over a Noetherian base; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-per-supported-generators-costalk-detection: the existing statement concerns Detection of supported cohomology bounds by geometric costalks in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-per-trait-dualizing-scalar-restriction: the existing statement concerns Scalar endomorphisms of the relative dualizing complex over a complete trait; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-pc-affine-derived-pushforward-sheaf-edge: the existing statement concerns Affine sheaf-level derived edge normalized by the right-derived unit in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pc-coproduct-truncation-couple: the existing statement concerns Natural coproduct truncation exact-couple comparison in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pc-derived-bottom-unit-normalization: the existing statement concerns Bottom-cohomology comparison normalized by the actual right-derived unit in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pc-natural-bounded-below-truncation-couples: the existing statement concerns Individual bounded-below truncation couples with natural comparisons in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pc-raw-truncation-couple-naturality: the existing statement concerns Naturality of raw truncation maps for one derived morphism in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-affine-algebra-upper-truncation-edge: the existing statement concerns Canonical affine edge on upper truncation in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-derived-lower-truncation-cycle-formula: the existing statement concerns Canonical bottom derived comparison on cycle classes in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-derived-lower-truncation-unit-bridge: the existing statement concerns Bottom derived unit through good lower truncation in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-kinjective-section-cycle-comparison: the existing statement concerns Canonical cycle quotient comparison from derived lower truncation in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-left-exact-truncation-cycle-formula: the existing statement concerns Underived left exact lower truncation on cycles; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sc-left-exact-upper-truncation-comparison: the existing statement concerns Raw and derived upper-truncation comparisons in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sc-perfect-ext-bounded-qcoh-vanishing: the existing statement concerns Maps from a perfect complex vanish against a bounded quasi-coherent gap; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-affine-derived-sections-truncated-bottom: the existing statement concerns Lowest cohomology of truncated derived affine sections; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-def-pc-derived-bottom-comparison: the existing statement concerns Specified double-truncation bottom comparison in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-bottom-cycle-transport: the existing statement concerns Canonical cycles transported through double truncation to the actual single-object unit; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-bottom-inclusion: the existing statement concerns Every morphism from a single object factors through the bottom-homology inclusion; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-bottom-unit-normalization-formula: the existing statement concerns Canonical-cycle formula for the specified bottom comparison in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-cycles-map-homology: the existing statement concerns Homology of the localized canonical cycle map; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-cycles-unit-naturality: the existing statement concerns Derived-unit naturality on the canonical cycle map in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs new-lem-pc-derived-single-shift-normalization: the existing statement concerns The actual unit on a single object normalized in every integer degree in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs new-qcoh-acyclic-sections-component: the existing statement concerns Affine-open section comparison component; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs new-qcoh-sections-left-exact-bottom: the existing statement concerns Left exact bottom cohomology after lower truncation in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pod-connected-constant-h0: the existing statement concerns Degree-zero cohomology of the constant coefficients on a connected scheme; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-pod-constant-tower-transition: the existing statement concerns Degree-zero direct-image comparison is compatible with coefficient restriction in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pe-classical-derived-image: the existing statement concerns Classical cohomology of comparison inverse image; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sp-shift-identification: the existing statement concerns Shift rule for derived functors in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sp-truncation-abutment-cocone-aux: the existing statement concerns Compatibility equations for truncation cocone; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sp-truncation-abutment-cocone: the existing statement concerns Canonical normalized truncation cocone in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-coherent-affine-base-change-edge-naturality: the existing statement concerns Affine coherent edge isomorphisms compatible with base change; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor: the existing statement concerns Isomorphism of the degree-zero cycle factor; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-cohomology-pullback-degree-zero: the existing statement concerns Degree-zero cohomology and the degree-zero pullback map; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-adjunction-top-edge: the existing statement concerns Top cohomology of a derived adjunct and the local direct-image edge; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-functor-map-via-lift: the existing statement concerns Right derived functors on morphisms are computed by lifts to injective resolutions in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-functor-negative-vanishing: the existing statement concerns Right derived functors move to the right in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-functor-truncation-iso-epi: the existing statement concerns Low-degree derived cohomology map is epi; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-functor-truncation-iso-mono: the existing statement concerns Low-degree derived cohomology map is mono; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-functor-truncation-iso: the existing statement concerns Low-degree cohomology of a right derived functor sees only low degrees in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-derived-pullback-top-cohomology: the existing statement is about scheme-module pullback, truncation, and its adjunction-normalized comparison; the new node treats arbitrary right exact additive functors and object acyclicity, without a scheme, pullback, or adjunction hypothesis.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-heart-test-bounded-below: the existing statement concerns A heart test for bounded-below left t-exact transformations; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-horseshoe-delta-functor: the existing statement concerns The connecting maps of right derived functors computed from horseshoe resolutions are well defined and natural in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-left-exact-injective-resolution-degree-zero: the existing statement concerns Injective resolutions exist, and a left exact functor is recovered in degree zero in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-leray-acyclicity-quasi-iso: the existing statement concerns Leray's acyclicity lemma: a left exact functor preserves quasi-isomorphisms between bounded-below complexes of acyclic objects in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-right-derived-universal-delta-functor: the existing statement concerns Right derived functors form a universal delta-functor in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-weil-pbc-truncation-cohomology: the existing statement concerns Cohomology of the canonical truncation; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lemma-weil-pbc-exact-couple-abutment: the existing statement concerns Finite rows and the abutment comparison; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lemma-weil-pbc-hypercohomology-convergence: the existing statement concerns Half-plane convergence; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs sk-thm-acyclicity: the existing statement concerns Acyclic resolutions in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs sk-thm-properbasechange: the existing statement concerns Proper base change on classical pro-étale complexes; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs thm-sp-truncation-e2: the existing statement concerns The truncation hypercohomology spectral sequence in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sf-locally-closed-closure-adjoint-realization: the existing statement concerns Closure compactification realizes the immersion adjoint and its bounds; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-weil-boundary-etale-adjunction-restriction: the existing statement concerns Finite-dimensional compactifications and bounded-below restriction of etale adjunctions; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sfb-finite-proper-classical-amplitude: the existing statement concerns Uniform amplitude of proper direct image on classical finite-coefficient complexes; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sbc-base-change-homology-zero-underived: the existing statement concerns Degree-zero homology exchange is isomorphic to the underived exchange; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sbc-right-derived-base-change-zero-unit: the existing statement concerns Degree-zero derived base change respects the augmentations in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sbc-right-derived-single-unit-homology-comparison: the existing statement concerns RightDerivedSingleUnitHomologyComparison in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-sbc-strict-henselian-constant-hzero: the existing statement concerns Degree-zero cohomology of a constant sheaf over a strictly henselian local ring; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sbc-strict-henselian-constant-sections-natural: the existing statement concerns Naturality of constant sections over a strictly henselian local spectrum; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs sbc-thm-cohomological-dimension-of-an-affine-curve: the existing statement concerns Affine-curve cohomological dimension; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs fin4-thm-finite-morphisms-constructible: the existing statement concerns Finite morphisms preserve constructibility; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-exc-equivalence-derived-sections: the existing statement concerns Derived section functors under an additive equivalence in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-kun-geometric-point-derived-sections-adjunction: the existing statement concerns Derived geometric-point direct image is global sections with its adjunction; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-kun-right-derived-single-h0: the existing statement concerns Zeroth homology of the canonical right-derived single augmentation in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-pur-exact-derived-adjunction-bounds: the existing statement concerns Exact derived adjunctions: lower bounds, reflection and counits; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sf-etale-origin-pushforward-amplitude: the existing statement concerns Etale heart bounds control cohomological ranges on pro-etale complexes of etale origin; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sf-integral-direct-image-constructible: the existing statement concerns The integral derived direct image of a constructible complex along a finite-type morphism is constructible; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-sp-finite-compact-support-domains: the existing statement concerns Compact support and coefficient extension retain the finite-Tor domain; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-trf-bounded-above-acyclic-derived-computation: the existing statement concerns Bounded above acyclic complexes compute a left derived functor; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-trf-comparison-truncated-cohomology: the existing statement concerns Cohomology comparison through a vanishing bound in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-trf-left-acyclic-short-exact: the item concerns two closure properties and exactness for a short exact sequence; the new node concerns the total counit and cohomology of a single object and states neither closure property.

lem-trf-left-derived-object-cohomology vs lem-trf-nearby-proper-hyperdescent: the existing statement concerns Truncated nearby-cycle descent along a proper hypercover; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

lem-trf-left-derived-object-cohomology vs lem-trf-oriented-derived-cohomology-continuity: the existing statement concerns Continuity of bounded-below cohomology of oriented etale products in the right-derived/left-exact setting; the new node is the left-derived/right-exact single-object counit normalization and negative-cohomology criterion. Applying the existing statement would require an additional opposite-derived comparison, not a one-line specialization.

lem-trf-left-derived-object-cohomology vs lem-trf-oriented-nearby-hypercover-spectral-sequence: the existing statement concerns Proper hypercover descent for nearby cycles; it does not state the arbitrary right exact total-derived single-object counit normalization, positive vanishing, and negative-cohomology criterion of the new node.

## Validation repairs

The first server dry run rejected the phrase "the item's" in step 3 as a standalone-context ambiguity (B2). Replaced it with the explicit assumed everywhere-definedness of LV; also made step 1 refer to the hypotheses stated above. The mathematical statement, steps, dependencies and citation manifest are otherwise unchanged.
