# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-global-trace-adjunction.json: item, split into four steps; statement and stmt_deps retained exactly; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-global-hom-cup-comparison.json: one new statement-only lemma, unsplit; no Mathlib match. This constructs the general ringed-site map and records its action on shifted Hom, without asserting invertibility.
- citations.json: one verbatim statement quote for every cited node in every proof step.

## Attachments

None. Searched WeilConjectures for the blueprint tag, global trace, affine trace, global Hom and the related adjunction declarations. MixedGlobalHomAdjunctionIso.lean concerns schemes and Zariski structure modules, so does not attach an algebraic-space/small-etale statement. AffineHomComplexEvaluation.lean concerns an affine scheme morphism and an underived Hom-complex comparison, also not this item.

## WANTED

None. Read the locally available Stacks sources.

## Findings and corrections

The item was unsplit, with no earlier sandbox node or report and no repair note. Its statement is correct, including unbounded L, arbitrary A and the warning that internal Hom need not have quasi-coherent cohomology. No STATEMENT-DISPUTED correction was necessary. Retained all pre-existing searches, source, creation provenance, blueprint fields and statement dependencies. New searches were actually run through msearch.py and their results read; searches.jsonl records them. Returned ordinary Gamma/Spec adjunction, ordinary sheaf sections, condensed internal Hom, Ext functoriality and derived-category infrastructure are not this statement or the new comparison lemma.

The existing lem-sfb-space-global-hom-right-adjunction already supplies space global duality for an arbitrary target F. I did not create another duality node, nor use it to turn the present proof into a one-line restatement. Instead the supplied adjunction is used directly on Hom sets in step 3. Its existing affine module realization is reused. The genuinely missing input is the general cup/evaluation comparison and its normalization, which applies to all small ringed sites, all scalar rings and all unbounded L,M and need not be invertible.

Read dag/chapters/sec-six-functors-basics.json, dag/units/sk-thm-sf-ctf-stability.json, and the current blueprint latest (7284bb09daf97437d544c51882b325f9c52cd345), its unit section and direct-images proof. This is the inherited coherent-duality prerequisite below the unit's direct-image route, not a change of unit or chapter. The ancestry command reports from.node = None: the live chain ends at the absent created.item Sheaf.SixFunctors.CtfStabilityDirectImages. Preserved that inherited null and the complete place/via chain; did not invent a blueprint ancestor. Whole-DAG and blueprint searches for global Hom, trace adjunction, cup evaluation, RSheafHom, 08JA and 0B6D found no exact replacement for the new general comparison.

Source detail: spaces-duality.tex Tag 0E59's proof has a typographical second displayed formula, writing an O_X internal Hom on Y with a(K). Its statement and Tag 0E58 correctly use RHom_Y(Rf_*L,K). The delivery uses that typed expression; the item itself has no such error.

## Unfinished work

No unresolved part of the item. The new lemma is intentionally statement-only, as required for a one-level split. It will require the standard adjunction-triangle proof when split. No Lean files were written or compiler, Lake or build commands run. No repository or launcher files were edited.

## Review by N9

I read spaces-duality.tex equation-sheafy-trace, all of the proof of 0E58, the qualification 0GG4 and the global argument 0E59. I also read spaces-perfect.tex 071Q and sites-cohomology.tex 08JA, 08J9, 0B6C, 0B6D and 0D6E. The source's coherator is essential for a sheaf-level isomorphism. Global cohomology can instead be tested on shifts, and the present proof does precisely that; it never identifies arbitrary internal Hom with a quasi-coherent object.

For step 1 I opened lem-weil-pbc-ringed-topoi-derived-pushforward-composition: its statement gives the canonical natural composition isomorphism on unbounded ringed-site modules, so it applies to f followed by Y's global-sections morphism with the actual A-action. I opened lem-sfb-affine-etale-derived-module-realization: it explicitly gives the unbounded D(A) equivalence and its RΓ quasi-inverse for an arbitrary commutative ring, so no Noetherian or boundedness hypothesis is being imported. I opened lem-sf-ringed-derived-closed-symmetric-monoidal: its last sentence identifies transpose with evaluation after u tensor identity. Together with the new lemma's specified cup/evaluation pairing, that proves that postcomposition by t has exactly the advertised adjunct, not merely some isomorphism with the same endpoints.

For step 2 the new lemma states explicitly that its degree-n map is u ↦ G(u), including the canonical shift comparison. The composition node states naturality in the derived argument, so its square on u and on the counit changes this to G_Y(epsilon[n] Rf_*u). Target Hom cohomology is obtained on the one-object A-site. This is not inferred from an equality of unmarked abstract isomorphisms. The source of the new lemma is 0B6D's actual evaluation/cup construction, and 08JA's K-flat/K-injective identification; on a class u, uncurrying followed by the two pullback/pushforward triangles gives G(u). Its claim is independent of duality and is strictly smaller than the item.

For step 3 the only theorem used beyond the supplied hypothesis is the same affine equivalence, whose full faithfulness supplies the last Hom bijection. The adjunction is applied to O_Y[n], with the induced shift on its right adjoint; this avoids silently requiring a to have chosen extra shift data. The relevant quasi-coherent categories are full and shift-stable by the statement's definition. This is a direct application of the supplied adjunction, so the step is elementary and no duplicate adjunction lemma is created. Step 4 uses the localization definition in def-weil-abstract-derived-category: on a roof whose left arrow is a quasi-isomorphism, invertibility in cohomology forces its right arrow to be a quasi-isomorphism too. Both invert in D(A). The four steps have lengths 636, 578, 651 and 507 characters; none conceals a long inline lemma.

I checked all B1-B10, C1-C8, D1-D5 and E1-E7 requirements against these files and sources. The new node is self-contained, all bracketed notions are statement dependencies, proof and proof_deps are empty, and its derived comparison is a morphism of objects in D(A), not just separate cohomology assertions. It does not restate an item clause: without a right adjoint or any geometric assumption it only constructs a map which can fail to be an isomorphism. The final duality still comes from the item's own adjunction argument. I checked that the cited dependencies do not reach the item, so no cycle is introduced. Off-unit uses are declared as generic tool uses in split_report, not written to the maintainer-owned tool_uses field.

Small cases checked: on the one-object A-site with p the identity, the new chi is identity on derived Hom and acts as identity in every degree; for L=0 or M=0 the map is the unique zero map between zero objects; for nonzero shifts the formula is G(u) with Hom on the left of tensor, so no extraneous Koszul sign is introduced. For the item f=id, a=id, tau is identity under the affine equivalence. For X empty both global objects are zero. No perfectness of L, properness of f, flatness of f, or Noetherianity of A was used. An infinite or nonperfect L is allowed because invertibility is proved after global sections, not by erasing the coherator from internal Hom.

## Not duplicates

- lem-sfb-ringed-global-hom-cup-comparison vs lem-coef-scalar-hom-zero-compatibility: compares scalar-change internal Hom in degree zero, rather than the direct image to a scalar point in every degree.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-weil-boundary-evaluation-currying: its assertion concerns ringed-site exceptional evaluation and opposite currying; no general unbounded ringed-site global-sections Hom comparison with the specified cup transpose is asserted.
- lem-sfb-ringed-global-hom-cup-comparison vs def-coef-hom-zero-cycle-class: defines canonical zero-cycle class in derived global hom; it does not assert the new general direct-image cup/evaluation comparison or its shifted action.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-coef-etale-hom-transpose-exact: its assertion concerns reversed exactness of the specified étale hom transpose; no general unbounded ringed-site global-sections Hom comparison with the specified cup transpose is asserted.
- lem-sfb-ringed-global-hom-cup-comparison vs def-wf-ordinary-etale-cup: defines ordinary integral cohomology cup for schemes and abelian sheaves; no derived Hom comparison.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pc-derived-tensor-hom-sections-unit: identifies degree-zero Hom classes using the tensor unit; explicitly involves no direct-image functor or adjunction.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pc-derived-pullback-evaluation-sections: applies scheme derived pullback to Hom and compares hypercohomology; the new node applies derived global direct image and uses its lax cup map.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-derived-internal-hom-shift-right: compares shifts of internal Hom or its resolution models; it does not construct the global direct-image comparison chi.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sc-global-hom-shifted-hypercohomology: relates shifted cohomology and hypercohomology for a scheme, not the cup/evaluation map to Hom of sections.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sc-restricted-global-hom-shifted-equiv: identifies shifted global Hom groups for schemes, without the comparison to Hom of global sections.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-derived-internal-hom-shift-left: compares shifts of internal Hom or its resolution models; it does not construct the global direct-image comparison chi.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-hom-complex-resolution-shift-comparison: compares shifts of internal Hom or its resolution models; it does not construct the global direct-image comparison chi.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-derived-internal-hom-shift-comparison: compares shifts of internal Hom or its resolution models; it does not construct the global direct-image comparison chi.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sfb-derived-internal-hom-sections-model: provides the global Hom complex and its cohomology, not its map to Hom of two global-section complexes or the cup/evaluation normalization.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sfb-module-object-ringed-site-derived-comparison: its assertion concerns module-object and ringed-site derived internal hom agree; no general unbounded ringed-site global-sections Hom comparison with the specified cup transpose is asserted.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sfb-component-slice-hom-comparison-test: concerns component inverse image from profinite slices; neither its functor nor its coefficient ring is the general ringed-site global direct image.
- lem-sfb-ringed-global-hom-cup-comparison vs def-per-ordinary-kummer-first-chern: defines ordinary derived kummer first chern class; it does not assert the new general direct-image cup/evaluation comparison or its shifted action.
- lem-sfb-ringed-global-hom-cup-comparison vs def-weil-pbc-adic-global-derived-hom: defines global derived hom for completed adic coefficients; it does not assert the new general direct-image cup/evaluation comparison or its shifted action.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-weil-pbc-proetale-internal-hom-lower-bound: is a t-structure amplitude bound on internal Hom; no cup/evaluation direct-image comparison.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-weil-pbc-derived-hom-sheaf-comparison-lisse: is an etale/pro-etale local morphism-sheaf comparison under bounded finite-locally-constant hypotheses.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-external-rhom-signed-cones: concerns external tensor pairings or their cone/braiding normalization, not the general internal Hom map induced by derived global sections.
- lem-sfb-ringed-global-hom-cup-comparison vs def-pur-external-rhom-pairing-interface: defines external global hom evaluation interface; it does not assert the new general direct-image cup/evaluation comparison or its shifted action.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-external-rhom-derived-braiding: concerns external tensor pairings or their cone/braiding normalization, not the general internal Hom map induced by derived global sections.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-global-hom-evaluation-model: requires a scheme, constant coefficient ring, and bounded flat source; constructs a Hom-complex model, not the new general global-sections Hom comparison.
- lem-sfb-ringed-global-hom-cup-comparison vs def-pur-ringed-site-zeroth-hypercohomology: defines zeroth hypercohomology on a small ringed site; it does not assert the new general direct-image cup/evaluation comparison or its shifted action.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-hom-kflat-into-kinjective: is K-injectivity of a sheaf Hom complex, not functoriality of a global-sections Hom comparison.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-hom-complex-global-homotopy: identifies ordinary global cochain H0 with homotopy classes; does not compare derived sections of Hom with module derived Hom.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-rhom-global-sections: identifies H0 of global RHom with derived Hom but does not construct chi or identify its map on cohomology.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pur-hom-complex-hypercohomology: identifies hypercohomology of Hom with homotopy classes into K-injectives; no comparison chi.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-pod-cup-product-graded-commutativity: proves graded commutativity for proper smooth varieties with rational coefficients, not the unbounded A-linear global Hom comparison.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sfb-space-global-hom-right-adjunction: the existing node is geometric duality with a supplied right adjoint and asserts invertibility; the new map is for arbitrary ringed sites and arbitrary L,M and makes no invertibility claim.
- lem-sfb-ringed-global-hom-cup-comparison vs lem-sc-mixed-global-hom-adjunction-isIso: the existing node is duality for qcqs Zariski schemes; the new node is the general global-sections cup/evaluation construction and does not assume a duality adjoint.
