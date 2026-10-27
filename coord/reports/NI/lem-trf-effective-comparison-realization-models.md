## Worker report

Files written (all beneath this item's NI sandbox):

- dag/nodes/sec-trace-formula/lem-trf-effective-comparison-realization-models.json: existing statement, unchanged statement and stmt_deps; three-step assembly, 1,409 characters.
- dag/nodes/sec-trace-formula/lem-trf-roos-adjunction-quotient-normalization.json: statement, unsplit, no Mathlib match; former steps 1, 2, 5.
- dag/nodes/sec-trace-formula/lem-trf-primitive-quotient-realization-comparisons.json: statement, unsplit, no Mathlib match; former steps 3, 4.
- dag/nodes/sec-trace-formula/lem-trf-effective-quotient-model-descent.json: statement, unsplit, no Mathlib match; former steps 6, 7, 8.
- citations.json: verbatim statements for every citation in all three assembly steps.
- report.md and searches.jsonl: this report and the actual msearch log. The sandbox scripts and duplicate-candidates.json are working aids, not delivery files.

Attachments: none. I searched lean/WeilConjectures for the blueprint id and realization/model notions; there is no exact project declaration there. The recorded Sheaf.Paper.EffectiveComparisonRealizationModels declaration at lines 194–196 is still `by sorry`, so it is not an attachment.

WANTED: none. This is an agent refinement of sources present locally, not a claim that a Stacks tag states the entire simultaneous interface verbatim.

The released stage-1 repair note dated 2026-10-22 is the authority for re-splitting the already reviewed node. It requires at least two comparable new unsplit nodes, a parent assembly under 3,000 characters, and preservation of every old argument. Three blocks now distribute the eight arguments, including the original sources, uses, elementary flags and text stored verbatim as `split_report.retained_arguments` in the respective new node. Each new node has empty proof/proof_deps and null proof_origin. This provenance is not a completed split. The order explicitly overrides the usual prohibition on extracting a clause and the live-wins rule; I have not merely renamed the whole item in one child.

No statement correction or dispute was needed. I corrected the scalar comparison direction when spelling out its construction: association maps the scalar-system cone to the defining scalar-operation cone, so the primitive map from the latter to the former realization is rho composed with H(association) inverse. The old proof's words "compose the identification" had left that direction implicit. The old argument is retained unaltered as provenance.

Current blueprint check: `literature/blueprint/latest` points to main-20261024. I opened its trace-transport _section.md and sk-thm-trace-transport.proof.md. The latter now derives the Euler-product formula from sk-thm-tf-uniform-formula; prop-trf-karoubi-independence is no longer in the newest snapshot. The imported DAG ancestor remains prop-trf-karoubi-independence, as blueprint_refs.py ancestor confirms. I preserved that ancestry and recorded the disappearance in every new blueprint.from.place and the parent split_report, rather than citing an older snapshot as current or changing the repair route. I searched the whole imported blueprint with blueprint_refs.py for Roos, scalar realization, quotient augmentation, effective comparison and normalized reconstruction. No imported node states one of the three extracted combined assertions. The Roos search returned general limit definitions, a Roos triangle and completion results, not these actual normalized model packages. I also searched all DAG nodes for the source tags and model/counit keywords and opened the candidate statements discussed below.

Mathlib searches: each new node has its own semantic questions in two phrasings, LeanSearch, Loogle and source grep, all actually executed by msearch.py and read. The primitive block's first Loogle query used an unknown DerivedCategory identifier; its record says invalid query and records the replacement successful SheafOfModules.pullbackComp query. Ordinary pullback composition in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167, abstract Adjunction.toEquivalence in Mathlib/CategoryTheory/Adjunction/Basic.lean:676, and IsKInjective.Qh_map_bijective / quasiIso_iff in Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41,50 were read. These do not state the new assertions even by a one-line specialization: they lack the actual quotient-system completed models and their reconstruction. I read ElladicCohomology.lean:61–78 as well; it defines the coefficient sheaf and ordinary cohomology, not normalized system effectivity. Searches returned algebraic etale and cotangent constructions, mapping-cone comparisons and condensed solidification facts, none with the quotient-system assertions. No unavailable service was recorded as no match. The parent's previous search records are retained because its statement and search question are unchanged.

Nothing remains unfinished within this stage-1 delivery: the child proofs are deliberately future work. No Lean file was written and no compiler, Lake or build tool was run.

## Review by NI

I read the repair order, the parent statement and all eight existing steps, all twenty statements those steps cite, and delivery-errors.md B–E. I read Stacks proetale.tex Tag 099N, lemma-pushforward-Noetherian-case (2),(5), with its completed pullback formula; sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, including the K-injective resolution, surjective injective transitions and product-cone argument; Tag 06YS, lemma-K-flat-resolution; Tag 0G7E, lemma-pullback-K-flat; and Tag 0D6D, lemma-derived-pullback-composition. These are the sources for the parent and for the extracted Roos, quotient-model and descent constructions. The specialized effectivity and constructibility inputs are the existing DAG statements, not an extra conclusion attributed to those Stacks lemmas. The latest blueprint check is described above; I did not consult an older snapshot as a substitute.

Assembly step 1 uses precisely lem-trf-roos-adjunction-quotient-normalization. Its statement supplies rho on the entire derived tower category, [q] inverse after the ordinary limit cone as the counit adjunct, and u_K = rho[v_P][p] inverse with zero shifted coordinate. Thus the step does not replace a whole-system map by a set of unrelated evaluated maps. The old inputs were opened: exact countable pro-etale products meet the strict Roos comparison hypothesis; the system-calculus statement actually gives R adjoint to L and the evaluated counit; the strict tower limit computes on a K-injective tower; and completion-unit-strict-quotient-model states the entire-morphism equality, not merely its level projections. The argument z tensor 1 has (1-s)=0 is elementary and retained within the extracted statement and provenance, not made a fourth node.

Assembly step 2 uses precisely lem-trf-primitive-quotient-realization-comparisons. Its statement supplies both derived-category isomorphisms, their specified K-flat presentations, tensor generator formulas, quotient transition squares, the identity case and the three-field multiplication identity. This is enough for the assembly's primitive models. The old inputs say what is used: kflat-change-of-rings applies to any ring sheaf map and preserves flat terms; constant-exact says inverse image is exact and identifies finite constant rings; the completed operation definitions use those very quotient towers; coefficient-extension-reduction-model states the simultaneous scalar association, normalization and transitions without unramifiedness. I checked the comparison arrow direction explicitly, as noted above. No step commutes inverse image with an infinite product.

Assembly step 3 uses lem-trf-effective-quotient-model-descent and def-trf-integral-comparison-realization-models. The former is conditional on the particular constructions fixed in steps 1–2; it supplies normalization, invertibility of the actual counits and unit, membership in the two C categories and simultaneous natural descent. The latter defines exactly the interface being assembled. Their quoted statements therefore say every clause the step takes. For its inherited arguments I verified the normalized-actual-reconstruction statement has no boundedness or Tor assumptions, inverse-image tensor closure concerns the actual transition adjuncts, and the scalar reduction model permits arbitrary ambient K and ramification. The preservation results state respectively arbitrary f pullback and finite integral extension on the same D^b_c category, including the required uniform interval. The two well-definedness statements explicitly give descended functors and natural comparison isomorphisms on K-flat representatives. Naturality of rho and of the actual adjunction then gives resolution independence of the composites. Those are facts stated by the cited inputs, not facts taken from their proofs.

Small cases checked for every new statement: K=0 gives zero towers/maps and the identity isomorphism of zero objects; n=1 changes no formula; f=id recovers the same quotient tower and completion; E=L gives scalar multiplication and the usual reduction counit; the empty scheme has trivial module categories and all formulas remain valid. For a ramified quadratic extension with uniformizer pi_L satisfying pi_L squared = ell, the map A_E,2 to A_L,2 kills ell and need not be flat. The argument still computes its derived tensor using the K-flat source quotient complex; neither scalar associativity nor normalization uses flatness of that ring map. Arbitrary unbounded ambient K is allowed in the first two children and the normalization part of the third, but constructibility is asserted only after the explicit K in C_E hypothesis. The actual unit is not claimed invertible for arbitrary noncomplete K. Small skeletons and the module-universe assumption are explicit, so no large indexing category has silently entered a cited small-limit theorem.

I checked B1–B7 on the three new statements: every scheme, field, complex, system, ring, functor and map is introduced, all specialized notions have explicit dependency citations, sources use the named labels and tags, TeX has single mathematical backslashes after JSON decoding, and no new statement is elementary. The derived comparisons are stated as derived isomorphisms, not only cohomology-degree identifications. The three child sizes are comparable (approximately 3.0k, 3.7k and 4.3k statement characters before any later edit). All eight old text arguments occur exactly once in the three retained_arguments lists. There is no claim that a statement-only new child is already proved. The assembly has no step over 2,000 characters. This is a one-level repair under the explicit spreading-work order.

The old generic tool lemmas are still cited verbatim in the retained arguments and as necessary statement dependencies, but the parent now uses only same-unit children and the interface definition. Its pre-existing maintainer-owned tool_uses and review records are retained; no new maintainer approval was invented. No chapter or unit file was changed. Check_dag and the complete delivery dry run will check the graph and scope at delivery time.

## Not duplicates

lem-trf-effective-quotient-model-descent vs lem-pe-kflat-roos-representative-invariance: only augmented scalar Roos quasi-isomorphism invariance; it gives neither pullback/system counit models nor constructible effectivity.

lem-trf-effective-quotient-model-descent vs lem-sfb-ringed-finite-free-resolution-tensor: bounded-above specified finite free resolution and its tensor differential; it gives no whole quotient-system realization comparison.

lem-trf-effective-quotient-model-descent vs lem-sbc-koszul-tensor-derived-tower: identifies an ordinary Koszul tensor tower with a derived tensor tower; the present towers are actual coefficient quotients, with primitive model/counit data.

lem-trf-effective-quotient-model-descent vs def-sbc-strict-projection-tower-data: defines normalized projection/direct-image data, rather than constructing the specified quotient reduction adjunction or its effective realizations.

lem-trf-effective-quotient-model-descent vs lem-sbc-scalar-extension-counit-properties: one scalar extension universal derived counit on K-flat complexes and its shifts; not the reduction/realization adjunction for a quotient diagram.

lem-trf-effective-quotient-model-descent vs lem-sf-cochain-tensor-model-rigidity: uniqueness of binary derived tensor presentations under localization; no actual quotient tower Roos model or effective counit.

lem-trf-effective-quotient-model-descent vs lem-fix-bounded-projective-tensor-complete: completion of bounded projective sheaf tensors on a qcqs scheme; the present ambient complexes are unbounded and need not be perfect, and the assertion also compares pullback and scalar systems.

lem-trf-effective-quotient-model-descent vs def-sf-koszul-total-derived-limit: defines a Koszul total derived limit and Koszul completion; no actual quotient reduction adjunction normalization or model effectivity theorem.

lem-trf-effective-quotient-model-descent vs lem-sf-open-reduction-adjunction-transport: assumes reconstruction and transports the open extension/restriction adjunction; the present statement establishes effectivity/descent for arbitrary scheme maps and finite coefficient changes.

lem-trf-effective-quotient-model-descent vs lem-sf-open-square-quotient-augmentation: a fixed finite-type Cartesian open square and its augmented pullback comparison; no simultaneous coefficient-system adjunction or scalar model construction.

lem-trf-effective-quotient-model-descent vs def-coef-reduction-limit-shift-data: defines normalized shift data without asserting existence; here actual Roos/counit/unit models or their effective descent are asserted.

lem-trf-effective-quotient-model-descent vs lem-sf-product-normalization-realization-transport: conditional transport of compactified external-product word equations on finite-Tor inputs; the present models have no finite-Tor hypothesis and concern primitive pullback/scalar systems.

lem-trf-effective-quotient-model-descent vs lem-coef-derived-tower-counit-projections: constant-tower/limit derived adjunction and projections only; no quotient change-of-rings counit combined with the zero-shifted actual reduction unit.

lem-trf-effective-quotient-model-descent vs lem-sf-perfect-tensor-roos-completion: bounded finite projective complexes over a complete DVR on the one-point site; no arbitrary unbounded sheaf quotient-system adjunction models.

lem-trf-effective-quotient-model-descent vs lem-sf-roos-adjunction-unit-coherence: given exact product-preserving adjunction with invertible unit; the present completion unit need not be invertible on ambient objects and no product-preserving pullback is assumed.

lem-trf-effective-quotient-model-descent vs lem-coef-sequence-sections-limit-comparison: derived global sections versus total limit for a ringed sequence site; no actual coefficient reduction unit or primitive completed operation models.

lem-trf-effective-quotient-model-descent vs lem-coef-derived-system-evaluation-calculus: the specified quotient reduction/limit adjunction and its evaluations are inputs; the new extraction also supplies the strict Roos representative, actual K-injective tower formula, and zero-shifted full-morphism unit identification.

lem-trf-primitive-quotient-realization-comparisons vs lem-trf-effective-comparison-realization-models: the parent combines all model normalization, primitive comparisons, effectivity and descent; this extraction covers only its assigned block under the explicit human re-split order, with the other blocks independently assigned.

lem-trf-primitive-quotient-realization-comparisons vs lem-pe-kflat-roos-representative-invariance: only augmented scalar Roos quasi-isomorphism invariance; it gives neither pullback/system counit models nor constructible effectivity.

lem-trf-primitive-quotient-realization-comparisons vs lem-sfb-ringed-finite-free-resolution-tensor: bounded-above specified finite free resolution and its tensor differential; it gives no whole quotient-system realization comparison.

lem-trf-primitive-quotient-realization-comparisons vs lem-sbc-koszul-tensor-derived-tower: identifies an ordinary Koszul tensor tower with a derived tensor tower; the present towers are actual coefficient quotients, with primitive model/counit data.

lem-trf-primitive-quotient-realization-comparisons vs lem-sbc-scalar-extension-counit-properties: one scalar extension universal derived counit on K-flat complexes and its shifts; not the reduction/realization adjunction for a quotient diagram.

lem-trf-primitive-quotient-realization-comparisons vs lem-sf-cochain-tensor-model-rigidity: uniqueness of binary derived tensor presentations under localization; no actual quotient tower Roos model or effective counit.

lem-trf-primitive-quotient-realization-comparisons vs lem-sf-open-square-quotient-augmentation: a fixed finite-type Cartesian open square and its augmented pullback comparison; no simultaneous coefficient-system adjunction or scalar model construction.

lem-trf-primitive-quotient-realization-comparisons vs lem-pe-kflat-scalar-tower-realization: finite scalar-unit and transition computation on a single K-flat tower; no completed pullback primitive or simultaneous completed scalar realization isomorphism.

lem-trf-primitive-quotient-realization-comparisons vs lem-sbc-pullback-comparison-comp: composition of etale coefficient pullback/single-complex maps for a particular square; no completed quotient-system realization or scalar comparison.

lem-trf-primitive-quotient-realization-comparisons vs prop-weil-pbc-levelwise-truncations: truncation normalization under an explicit Tor-vanishing hypothesis, rather than primitive completed-operation models on arbitrary ambient objects.

lem-trf-primitive-quotient-realization-comparisons vs lem-sbc-completed-operations-linear-natural-exchange: linearity, adjunction and exchange for intrinsically complete objects; no K-flat quotient presentation normalization for whole-system pullback and ramified scalar realization.

lem-trf-primitive-quotient-realization-comparisons vs lem-sbc-reflected-compositor-unit-normalization: abstract reflected compositor/unit equation for supplied reflectors and adjunctions; not construction of primitive quotient realization models.

lem-trf-primitive-quotient-realization-comparisons vs lem-sf-open-exchange-roos-restriction: specific open base-change exchange and restriction equality; not construction of primitive pullback/scalar quotient realization maps.

lem-trf-primitive-quotient-realization-comparisons vs lem-coef-derived-system-evaluation-calculus: the specified quotient reduction/limit adjunction and its evaluations are inputs; the new extraction also supplies the strict Roos representative, actual K-injective tower formula, and zero-shifted full-morphism unit identification.

lem-trf-roos-adjunction-quotient-normalization vs def-sbc-strict-projection-tower-data: defines normalized projection/direct-image data, rather than constructing the specified quotient reduction adjunction or its effective realizations.

lem-trf-roos-adjunction-quotient-normalization vs lem-fix-bounded-projective-tensor-complete: completion of bounded projective sheaf tensors on a qcqs scheme; the present ambient complexes are unbounded and need not be perfect, and the assertion also compares pullback and scalar systems.

lem-trf-roos-adjunction-quotient-normalization vs def-sf-koszul-total-derived-limit: defines a Koszul total derived limit and Koszul completion; no actual quotient reduction adjunction normalization or model effectivity theorem.

lem-trf-roos-adjunction-quotient-normalization vs lem-sf-open-reduction-adjunction-transport: assumes reconstruction and transports the open extension/restriction adjunction; the present statement establishes effectivity/descent for arbitrary scheme maps and finite coefficient changes.

lem-trf-roos-adjunction-quotient-normalization vs lem-sf-open-square-quotient-augmentation: a fixed finite-type Cartesian open square and its augmented pullback comparison; no simultaneous coefficient-system adjunction or scalar model construction.

lem-trf-roos-adjunction-quotient-normalization vs def-coef-reduction-limit-shift-data: defines normalized shift data without asserting existence; here actual Roos/counit/unit models or their effective descent are asserted.

lem-trf-roos-adjunction-quotient-normalization vs lem-sf-product-normalization-realization-transport: conditional transport of compactified external-product word equations on finite-Tor inputs; the present models have no finite-Tor hypothesis and concern primitive pullback/scalar systems.

lem-trf-roos-adjunction-quotient-normalization vs lem-coef-derived-tower-counit-projections: constant-tower/limit derived adjunction and projections only; no quotient change-of-rings counit combined with the zero-shifted actual reduction unit.

lem-trf-roos-adjunction-quotient-normalization vs lem-sf-perfect-tensor-roos-completion: bounded finite projective complexes over a complete DVR on the one-point site; no arbitrary unbounded sheaf quotient-system adjunction models.

lem-trf-roos-adjunction-quotient-normalization vs lem-sf-roos-adjunction-unit-coherence: given exact product-preserving adjunction with invertible unit; the present completion unit need not be invertible on ambient objects and no product-preserving pullback is assumed.

lem-trf-roos-adjunction-quotient-normalization vs lem-coef-sequence-sections-limit-comparison: derived global sections versus total limit for a ringed sequence site; no actual coefficient reduction unit or primitive completed operation models.

lem-trf-roos-adjunction-quotient-normalization vs lem-coef-derived-system-evaluation-calculus: the specified quotient reduction/limit adjunction and its evaluations are inputs; the new extraction also supplies the strict Roos representative, actual K-injective tower formula, and zero-shifted full-morphism unit identification.


The first dry run selected additional same-tag candidates from the server index. I opened all of their statements (including the four detailed A1 augmentation/Roos lemmas) and checked the following distinctions; none supplies an extracted combined assertion. The added pairs repair that mechanical failure.

lem-trf-effective-quotient-model-descent vs def-a1-integral-completed-tower-pullback-universes: defines reduction and strict completed-ring pullback resolving pairs before realization; it asserts neither the primitive quotient-system realization comparison nor effective descended models.

lem-trf-effective-quotient-model-descent vs lem-a1-principal-koszul-strict-replacement: constructs an objectwise K-flat Koszul replacement of a quotient tower; not the completed whole-system pullback/scalar comparison or its constructible effectivity.

lem-trf-effective-quotient-model-descent vs lem-per-localized-pullback-tensor-normalization: compares scalar tensors after inverting one section on a ringed topos; no quotient inverse-limit realization or normalized-system effectivity is involved.

lem-trf-effective-quotient-model-descent vs lem-per-proetale-scalar-slice-comparison: commutes a single derived scalar extension with slice restriction; it supplies no completed quotient-system realization or actual reconstruction maps.

lem-trf-effective-quotient-model-descent vs def-fd-completed-scalar-shift-representative-property: defines shift-normalization predicates and expressly asserts no existence; the extraction constructs primitive realization maps or their effective descent.

lem-trf-effective-quotient-model-descent vs def-pc-derived-tensor-cohomology-vanishes: defines a cohomology-vanishing predicate for a scheme structure-sheaf derived tensor; it says nothing about actual quotient-system realization models.

lem-trf-effective-quotient-model-descent vs def-pc-derived-tensor-complex-cohomology-vanishes: defines a derived tensor cohomology-vanishing predicate, not completed operations or their normalized quotient-system models.

lem-trf-effective-quotient-model-descent vs def-pc-kflat-complex: defines K-flatness and K-flat resolutions; the extraction uses this notion to state a comparison construction and is not a second definition.

lem-trf-effective-quotient-model-descent vs def-sc-bounded-flat-shift-representative: a bounded-above flat homotopy-representative predicate; the extracted assertion concerns actual unbounded quotient-system realization maps.

lem-trf-effective-quotient-model-descent vs def-sc-derived-tensor-augmentation: defines a single tensor augmentation represented by a complex map; no actual completion unit, system realization or scalar/pullback comparison is constructed.

lem-trf-effective-quotient-model-descent vs def-sc-flat-telescope-stage-map: defines direct-sum telescopes and stage maps; the extracted assertions concern inverse quotient towers, products and derived realization.

lem-trf-effective-quotient-model-descent vs lem-pc-bounded-above-flat-kflat-site: only bounded-above flat implies K-flat; the extraction permits unbounded K-flat representatives and asserts quotient-model effectivity/descent.

lem-trf-primitive-quotient-realization-comparisons vs def-a1-integral-completed-tower-pullback-universes: defines reduction and strict completed-ring pullback resolving pairs before realization; it asserts neither the primitive quotient-system realization comparison nor effective descended models.

lem-trf-primitive-quotient-realization-comparisons vs lem-a1-principal-koszul-strict-replacement: constructs an objectwise K-flat Koszul replacement of a quotient tower; not the completed whole-system pullback/scalar comparison or its constructible effectivity.

lem-trf-primitive-quotient-realization-comparisons vs lem-per-localized-pullback-tensor-normalization: compares scalar tensors after inverting one section on a ringed topos; no quotient inverse-limit realization or normalized-system effectivity is involved.

lem-trf-primitive-quotient-realization-comparisons vs lem-per-proetale-scalar-slice-comparison: commutes a single derived scalar extension with slice restriction; it supplies no completed quotient-system realization or actual reconstruction maps.

lem-trf-primitive-quotient-realization-comparisons vs def-fd-completed-scalar-shift-representative-property: defines shift-normalization predicates and expressly asserts no existence; the extraction constructs primitive realization maps or their effective descent.

lem-trf-primitive-quotient-realization-comparisons vs def-pc-derived-tensor-cohomology-vanishes: defines a cohomology-vanishing predicate for a scheme structure-sheaf derived tensor; it says nothing about actual quotient-system realization models.

lem-trf-primitive-quotient-realization-comparisons vs def-pc-derived-tensor-complex-cohomology-vanishes: defines a derived tensor cohomology-vanishing predicate, not completed operations or their normalized quotient-system models.

lem-trf-primitive-quotient-realization-comparisons vs def-pc-kflat-complex: defines K-flatness and K-flat resolutions; the extraction uses this notion to state a comparison construction and is not a second definition.

lem-trf-primitive-quotient-realization-comparisons vs def-sc-bounded-flat-shift-representative: a bounded-above flat homotopy-representative predicate; the extracted assertion concerns actual unbounded quotient-system realization maps.

lem-trf-primitive-quotient-realization-comparisons vs def-sc-derived-tensor-augmentation: defines a single tensor augmentation represented by a complex map; no actual completion unit, system realization or scalar/pullback comparison is constructed.

lem-trf-primitive-quotient-realization-comparisons vs def-sc-flat-telescope-stage-map: defines direct-sum telescopes and stage maps; the extracted assertions concern inverse quotient towers, products and derived realization.

lem-trf-primitive-quotient-realization-comparisons vs lem-pc-bounded-above-flat-kflat-site: only bounded-above flat implies K-flat; the extraction permits unbounded K-flat representatives and asserts quotient-model effectivity/descent.

lem-trf-roos-adjunction-quotient-normalization vs def-a1-lisse-section-evaluation: defines H0 evaluation at a geometric point via common-stage Weil pullback; no existence of the normalized reduction/realization adjunction models is asserted.

lem-trf-roos-adjunction-quotient-normalization vs lem-a1-normalized-roos-shift-comparison: assumes the normalized Roos comparison and proves its signed-shift compatibility; the extraction constructs the actual quotient-system counit and unit normalization without asking a shift theorem.

lem-trf-roos-adjunction-quotient-normalization vs lem-a1-projective-quotient-augmentation: proves completeness for a bounded constant finite-projective scalar model; the extraction applies to all ambient complexes and includes the whole-system counit adjunct.

lem-trf-roos-adjunction-quotient-normalization vs lem-a1-quotient-unit-shift-completeness: assumes an invertible specified quotient augmentation and proves its shifts complete; the extraction computes the actual adjunction unit for arbitrary, potentially noncomplete K.

lem-trf-roos-adjunction-quotient-normalization vs lem-a1-roos-intrinsic-unit-comparison: compares intrinsic Koszul completion and strict quotient completion; the extraction adds the actual whole-system reduction/realization counit and K-injective tower-cone normalization, without asserting intrinsic completion comparison.

lem-trf-roos-adjunction-quotient-normalization vs lem-a1-signed-fiber-roos-normalization: compares two signed cone-coordinate conventions for a supplied rho and descends augmentations; the extraction computes the actual quotient reduction adjunction unit and whole-system counit.

lem-trf-roos-adjunction-quotient-normalization vs def-zl-field-weil-shriek-shift-data: defines rational/common-stage Weil compact-support shift data, not integral quotient reduction/realization adjunction models.

lem-trf-roos-adjunction-quotient-normalization vs def-fd-common-strict-tower-models: defines a comparison package for an isomorphism on common full integral constructible categories, explicitly asserting no existence; the extraction constructs normalization for arbitrary schemes and ambient complexes.

lem-trf-roos-adjunction-quotient-normalization vs def-fd-integral-pullback-shift-coordinates: defines pullback shift-coordinate and descent predicates, asserting no existence; the extraction constructs actual Roos/counit/quotient-unit models.

lem-trf-roos-adjunction-quotient-normalization vs lem-fd-pullback-augmentation-counit-matching: is restricted to noetherian finite-dimensional schemes and scheme isomorphisms and compares framework versus PBC pullback; the extraction gives the general quotient reduction adjunction unit/counit normalization without those hypotheses.

lem-trf-roos-adjunction-quotient-normalization vs lem-fd-pullback-common-strict-tower-models: framework/PBC comparison for noetherian finite-dimensional scheme isomorphisms; it does not give the arbitrary-scheme whole quotient reduction adjunction models.

lem-trf-roos-adjunction-quotient-normalization vs lem-fd-pullback-signed-shift-word-transport: shift and word equations assuming primitive comparisons on noetherian finite-dimensional isomorphisms; it does not construct the general quotient counit/unit normalization.
