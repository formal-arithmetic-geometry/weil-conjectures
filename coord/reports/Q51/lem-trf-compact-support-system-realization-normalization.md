## Files written

- `dag/nodes/sec-trace-formula/lem-trf-compact-support-system-realization-normalization.json`: repaired item with eight proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-compact-support-system-evaluation-coherence.json`: new statement-only strict/enhanced whole-system comparison; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-weil-isomorphism-derived-pullback-comparison-normalization.json`: new statement-only completion-unit normalization of the specified kappa; no Mathlib match.
- `citations.json`: verbatim statements for every cited node/step pair.

The previously delivered operation-normalization node was removed from this delivery because it restated the item's alpha/beta clause (D1). Its argument is now written in the item, with the canonical maps explicitly constructed there. The compactification-choice paragraph was removed from the evaluation-coherence support node for the same reason; step 1 now constructs the comparison directly from that node and the existing tower-functor node.

## Attachments

None. Searches of the project declarations for the item tag and for the two retained support statements found no sorry-free declaration stating them exactly. The upstream master sorry declarations are not finished proofs.

## WANTED

None.

## What was wrong and what changed

The return identified D1 for the generalized Frobenius-operation node and for the compactification paragraph of the evaluation-coherence node. It also identified undefined source/target comparisons, and C1/C4 in step 2. I repaired each point as follows.

1. Step 1 now constructs the whole-tower map from the strict/enhanced simultaneous model equivalence and the existing compact-support tower functor, including its actual evaluations, transitions, and morphism functoriality. The support node no longer repeats the item's compactification clause.
2. Step 2 cites `lem-weil-pbc-ringed-strict-tower-homotopy-limit` and explicitly applies its functorial total derived limit to the strict whole-system map. This supplies the coherent tower and morphism functoriality used there.
3. The item statement now defines the canonical source comparison by the concrete composite
   `L_Y(G_{Y,r}(e_C)) ∘ L_Y(b^Y_{r,H}) ∘ u_{P_{Y,r}H}`
   and the target comparison by `L_Y F((b^X_{r,K})^{-1})`. It then states that these are the operation-comparison maps named in the exchange definition. Step 7 expands these composites and proves the alpha formula using the specified completion-unit equation; beta is the displayed inverse-tensor formula, and the reduction node supplies preservation of the units, counits and tensor constraints.
4. The generalized operation-normalization support node was therefore not delivered. No step cites it, and the proof no longer substitutes the item into a clause-sized lemma.

## Review by Q51

I reread the item, the two retained new nodes, every node named in each proof step, the return entry, the current blueprint proof `prop-trf-rational-frobenius-integral-model.proof.md` (2)--(3), `def-weil-frobenius-square-exchange` item 2, `lem-fix-operation-reduction`, and `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. The item hypotheses remain the finite-field, coefficient, separated finite-type, compactification, bounded constructible and derived-complete hypotheses in the source; no hypothesis was added or dropped.

For step 1, the retained model-comparison statement gives a natural equivalence on every semilinear input and whole-tower isomorphism after restriction. The compact-support tower statement gives the actual finite evaluations, quotient transitions and naturality on morphisms. The step composes those specified maps, so it does not infer a tower map from equal evaluated arrows.

For step 2, the evaluation-calculus statement identifies `L_Y` with `R lim U_Y`; the integral compact-support definition supplies the same finite output system; constructibility supplies the bounded output. The strict-tower homotopy-limit statement supplies the functorial total-limit construction on whole strict maps, which repairs the prior unsupported claim of a coherent tower on morphisms.

Steps 3--5 were checked against the stated completion-unit normalization, K-flat pullback, explicit reduction-tower tensor map, the existing kappa compositor equation, and the specified integral pullback compositor. The domain checks are made in the text: `K` and its pullbacks are bounded constructible and derived complete. The tensor calculation is on strict quotient systems before localization, and the kappa algebra uses the actual specified maps.

Step 6 uses exact inverse image, preservation of K-injectives, the strict-tower total-limit model, the coefficient-projection square, and the specified kappa inverse. It constructs the limit comparison from one whole K-injective cone and uses no reconstruction isomorphism `R_Y H_f(K) ≅ C_f(K)`. Step 7 now reads the operation definition literally: the source comparison is the unit--tensor--counit composite written in the item, and the target comparison is the inverse tensor map followed by `L_YF`. The equation `theta ∘ kappa = G(u)` gives alpha equal to `omega ∘ kappa^{-1}`, while the definition of `v` gives beta equal to `L_Y(v)`. `lem-fix-operation-reduction` is cited only for preservation of the structural maps. Step 8 records naturality of these explicit maps and the compositor calculations.

I checked edge cases `K=0`, the zero system, identity scheme automorphisms, `r=1`, `m=1`, and an incomplete ambient object. The last case confirms that the completion-unit factorization does not assert invertibility outside the derived-complete domain. No finite Tor-amplitude condition was silently inserted. The two retained new nodes were searched in the whole DAG and blueprint and have the required three Mathlib search records; no Mathlib leaf is claimed and no forbidden SGA source is used.

## Not duplicates

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-weil-compact-support-reduction-tower-functor`: the former compares strict and enhanced semilinear operation models on arbitrary inputs; the latter supplies one compact-support tower and its finite evaluations.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-coef-derived-system-evaluation-calculus`: the former compares operation composites and adjunction structure; the latter defines the reduction/limit adjunction and evaluation calculus.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-inverse-image-pullback-comparison`: the definition only supplies the specified kappa map; the new statement identifies it with inverse image of the actual completion unit and proves invertibility on the complete domain.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `lem-weil-isomorphism-derived-pullback`: the existing statement uses an unspecified comparison isomorphism; the new statement fixes the specified kappa and its full cone normalization.

## What could not be finished

The two retained support lemmas are intentionally statement-only stage-1 nodes for later splitting. The repaired item and its citations are complete; the required dry run is the remaining delivery check.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-cbc-exact-product-functor-strict-limit`: both cite Tag 0940, but the existing node is an exact product/limit comparison and does not compare strict/enhanced operation models or adjunction maps.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-weil-ringed-tower-pushforward-limit-comparison`: the existing node concerns pushforward versus inverse limit; the new node compares strictification of semilinear operation composites on arbitrary inputs.

`lem-trf-compact-support-system-evaluation-coherence` vs `sk-lem-sp-tower`: the existing node reconstructs a normalized tower; the new node supplies a strict/enhanced model equivalence with units, counits and coefficient transposes.

`lem-trf-compact-support-system-evaluation-coherence` vs `def-weil-pbc-ringed-koszul-system`: the existing node defines a finite strict Koszul system; the new node is a comparison theorem for operation models.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-weil-pbc-ringed-cech-koszul-dual-limit`: the existing node gives a Cech/Koszul dual-limit presentation; the new node compares strict and enhanced semilinear composites.

`lem-trf-compact-support-system-evaluation-coherence` vs `def-coef-ringed-sequence-site`: the existing node defines the sequence site; the new node compares its operations with the enhanced section model.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-coef-finite-adjunction-diagram-realization`: the existing node realizes finite adjunction diagrams; the new node compares whole strict/enhanced compact-support composites for arbitrary systems.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-sf-integral-compactification-system-realization`: the existing node realizes normalized integral compactification systems under its own hypotheses; the new node compares operation models before imposing normalization.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-cbc-completed-pullback-triangles`: the existing node concerns pullback triangles; the new node concerns strictification of compact-support operations and adjunction maps.

`lem-trf-compact-support-system-evaluation-coherence` vs `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: the existing node computes total derived limits; the new node compares strict/enhanced operation models before taking those limits.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `lem-pe-kflat-roos-representative-invariance`: the existing node proves representative invariance of Roos cones; the new node identifies the specified kappa with inverse image of the completion unit.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-category-product`: the existing node defines products; the new node uses the full product/cone map to normalize kappa.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-derived-limit`: the existing node defines derived limits; the new node identifies a specific inverse-image/pullback comparison on the complete domain.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-inverse-system`: the existing node defines inverse systems; the new node proves a kappa/unit comparison for derived completed coefficients.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-pbc-common-stage-cones`: the existing node defines common-stage cones; the new node proves the specified kappa cone identity and invertibility criterion.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `def-weil-tower-transition-endomorphism`: the existing node defines the shift endomorphism; the new node normalizes kappa using the entire completion cone.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `lem-weil-derived-limit-existence`: the existing node proves existence/computation of derived limits; the new node concerns the specified inverse-image pullback comparison.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `lem-weil-pbc-rectangle-derived-limit`: the existing node passes a rectangle to a derived limit; the new node fixes the kappa comparison with the completion unit.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `prop-weil-pbc-rlim-functoriality`: the existing node states functoriality of derived inverse limit; the new node identifies kappa on a complete input.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `prop-weil-pbc-roos-triangle`: the existing node gives the Roos triangle; the new node gives the specified kappa/unit cone factorization.

`lem-weil-isomorphism-derived-pullback-comparison-normalization` vs `lem-sfb-left-complete-heart-upper-bound`: the existing node gives a left-completeness bound; the new node normalizes inverse-image pullback and proves kappa invertibility.
