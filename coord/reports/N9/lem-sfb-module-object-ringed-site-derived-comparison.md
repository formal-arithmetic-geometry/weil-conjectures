# Stage-1 report: lem-sfb-module-object-ringed-site-derived-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-module-object-ringed-site-derived-comparison.json: retained statement and the newer live six-step proof; refined Step 2 to cite a new normalized derived tensor-coherence result and wrote the resolution transport explicitly.
- dag/nodes/sec-six-functors-basics/lem-sfb-exact-tensor-functor-derived-normalization.json: statement, unsplit; no exact Mathlib match. No proof steps or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-exact-tensor-functor-derived-braiding.json: statement, unsplit; no exact Mathlib match. Native Koszul-braiding compatibility for the prescribed normalized derived comparison.
- citations.json: verbatim statement excerpts for all 16 step/node citation occurrences.
- report.md: this report.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and module-object/ringed comparison notion. The project theorem AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison in lean/Sheaf/Paper/ModuleObjectRingedSiteDerivedComparison.lean still ends in sorry. Its small internalMonoidal_eq_localization theorem proves only a definitional monoidal-instance equality, not the item's Hom, evaluation and slice conclusions. The generic upstream exact-derived-functor and braiding modules do not state the new normalized functor theorem.

## WANTED

None. All sources consulted are present locally.

## Findings and scope

This is the explicit human re-split assignment, even though the live item is already split and reviewed. The live node already contains Q63's 2306-character assembly, superseding the 6739-character proof described by the route note. I retained that repair, its statement, all statement dependencies, prior Mathlib searches, Lean bindings, blueprint metadata and reviewed/tool-use records. I extracted the two arguments still implicit in its Step 2: invertibility and monoidal coherence of the normalized exact derived tensor comparison, and compatibility with the independently given native Koszul exchange. Both new lemmas concern tensor functor localization, with no internal-Hom or slice conclusion. It does not move the whole item, global Hom comparison, evaluation comparison, or slice comparison into a new theorem.

The normalization statement uses an arbitrary exact strong monoidal left adjoint preserving flats and K-flat complexes; the separate braiding statement adds the ordinary symmetry equation. An equivalence is not required in either. Its normalization explicitly names the exact-functor factorization, the native K-flat tensor-model isomorphisms, and the ordinary total tensor comparison. This prevents an unspecified monoidal structure on E from standing in for the required comparison. The native signed braidings are fixed in the hypotheses. The proof remains a short assembly, with no step over 2000 characters.

The concrete proof declaration still has sorry, so there is no attachment. No Lean files were written, no compiler or build was run, and no repository or launcher files were changed. Only sandbox files were written. No agents were started.

## Source and search audit

For the item I read sites-cohomology.tex, equation-internal-hom and Tags 08JA (lemma-section-RHom-over-U), 08J9 (lemma-internal-hom), and 08JB (lemma-restriction-RHom-to-U), alongside the native derived tensor source at 0FPT and the current blueprint lem-sfb-dc-hom-preserves.proof.md. The coefficient/model comparison remains agent-written infrastructure before that blueprint's internal-Hom reduction. The mathematical route is unchanged. No SGA theorem is used in this delivery.

For both new nodes I read sites-cohomology.tex Tags 0FPQ (lemma-symmetric-monoidal-cat-complexes) and 0FPT (lemma-symmetric-monoidal-derived), the K-flat definition and derived tensor construction (06YU), and the existing exact-functor comparison statement. Stacks omits the coherence proofs at 0FPQ and 0FPT; the abstract normalized functor assertion is explicitly identified as an agent extraction, not claimed to be a verbatim Stacks theorem. The next worker's argument is: the normalization square exhibits t on K-flat representatives as a composite of isomorphisms; cochain associator and unit equations follow on total summands; exchanging bidegrees gives the same (-1)^(pq) on both sides because F is additive and symmetric; localization and naturality extend these equations to arbitrary derived objects. Unit coherence uses the actual degree-zero unit map. This sketch is recorded here, not in the unsplit node.

I searched the whole DAG by tensor equivalence, derived monoidal comparison, exact tensor functor, K-flat comparison, Koszul and the source tags, and ran tools/blueprint_refs.py ancestor and searches for derived monoidal equivalence, derived tensor comparison, K-flat, Koszul, braided, tensor comparison, exact tensor, strong monoidal, normalized derived tensor and module-object and ringed-site. No blueprint node states the new abstract normalized result. Its nearest ancestor is lem-sfb-dc-hom-preserves, via the item and lem-sfb-constructible-internal-hom-continuity, and its from.place names the coefficient/model identification before the first reduction calculation.

Every Mathlib search was run through the required msearch.py command and is in searches.jsonl. Both new nodes record the exact query strings and raw logged results for LeanFinder, LeanSearch, Loogle and grep, including alternate phrasings. I read Mathlib/CategoryTheory/Localization/Monoidal/Functor.lean and Braided.lean: functorMonoidalOfComp assumes the source localization functor is already strong monoidal on all its objects; cochain localization for a general derived tensor is only lax before restricting to K-flat objects. braidingNatIso_hom_app and beta_hom_app identify a single localized braiding, not the cross-functor normalized comparison here. Their use needs a K-flat restriction/localization identification and comparison equations, not a one-line specialization. Other hits were exact derived functors, ordinary transport of monoidal structures and signed total-complex flips. None is an exact Mathlib leaf for this statement.

## Review by N9

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files and sources. Each new node introduces both categories, the functor, its exactness/adjoint/flat-preservation hypotheses, both derived tensors, their braidings, and every map in its normalization square. Each has proof=[], proof_deps=[], proof_origin=null, status=unsplit. I checked its normalization square's domains: both sides start at E Q_C(P tensor Q) and end at Q_D(FP) tensor Q_D(FQ). The braiding square starts at E(K tensor L) and ends at EL tensor EK. The ordinary and derived unit maps both have the inverse-tensorator orientation. I did not assume arbitrary exact monoidal functors preserve K-flat complexes: this is an explicit hypothesis, verified for the section-action equivalence by the existing internal-section tensor comparison.

Step 1 uses lem-pe-internal-section-tensor-comparison for exactness and preservation/reflection of acyclicity, flats and K-flat complexes, and def-weil-exact-derived-adjunction for the specified localized unit and counit. Those statements say exactly this. Since the ordinary adjunction is an equivalence its localized unit/counit remain invertible. Smallness is the item's hypothesis, so there is no large-site application.

Step 2 uses lem-pc-sites-modules-functorial-flat-cover for a functorial epimorphism with flat values on the small ringed module category, lem-pc-kflat-resolution for a flat-term K-flat resolution of FK, and lem-pe-internal-section-tensor-comparison for reflecting flatness and K-flatness through the inverse equivalence. The displayed F^-1 C F construction is a natural flat cover: apply the inverse functor to the cover map and compose its counit; exactness preserves its epimorphisms. Likewise applying F^-1 to P -> FK and composing the counit gives the stated resolution of K; no object is chosen from a mere unproved existence definition. The normalization node supplies the normalized invertible t and its associator/unit equations; the independent braiding node supplies the signed exchange equation for that same t. An equivalence is a left adjoint, so all its functor hypotheses hold. This fixes the old unexplained sentence about preserving symmetry by the same summand equations.

Step 3 uses lem-sf-ringed-derived-tensor-hom-adjunction for the fixed closed structure and simultaneous model, lem-sf-ringed-derived-native-tensor for the native symmetry, and sk-def-sfb-derived-tensor-hom for the independently given internal adjunction. I checked the first lemma's site/coefficient/localization universe hypotheses and that it does not itself claim the symmetry; the separate native tensor citation provides it. Switching tensor order uses that symmetry, not a second Hom definition.

Step 4 uses lem-sfb-closed-scalar-hom-comparison, whose statement gives the natural comparison and its evaluation equation, not merely an objectwise isomorphism. At N=EL its comparison has type U H(EK,EL) -> H_A(K,UEL). Postcomposition with H_A(1,eta_L^-1) gives b into H_A(K,L); E(b^-1) followed by epsilon_H therefore has exactly the item's theta type. The scalar triangle identities cancel eta and epsilon in its stated transpose/evaluation equation. Contravariance in K is part of the comparison's naturality. Step 2's cited signed equation permits the Hom-first/native-counit convention to be rewritten in the item's tensor order.

Step 5 uses def-pur-localized-ringed-site for the literal section formula and small slice, def-sfb-internal-slice-derived-hom-comparison for native local structures and internal restriction as E_U^-1 r E, and lem-pur-site-restriction-module-adjunction-exact for exact r. Restriction-section compatibility is the counit of the actual slice equivalence. Repeating the general site argument is legitimate for B|U, not just for global objects in the image of restriction; the section-action comparison and flat-resolution nodes are stated for arbitrary sites and ring sheaves. Thus theta^U is natural on all local derived objects.

Step 6 uses lem-weil-pbc-ringed-slice-normalized-comparisons for existence of the four normalized data, and separately lem-weil-pbc-ringed-slice-evaluation-coherence for the required evaluation square. I checked that the first statement expressly does not give evaluation coherence and did not take it from that citation. Inserting the restriction-section counits in the displayed conjugation gives a natural isomorphism between E_U-images; full faithfulness lifts it uniquely and reflects its inverse. This is the single-slice square specified by the slice definition. No successive-slice cocycle is asserted.

For small-case tests I used the identity functor (t and the unit map reduce to identities), zero complexes (both sides of every square are the unique zero map), degree-zero unit complexes (both unit equations give ordinary multiplication/unitors), and a pair of rank-one complexes concentrated in odd degrees (both exchanges contribute -1). In characteristic two this sign becomes +1 on both sides. The empty ringed site and the zero ring cause no extra hypothesis: their module categories are zero categories. A nonexact scalar extension, such as Z -> Z/2, is excluded by the explicit exactness hypothesis and does not give a counterexample. The abstract theorem genuinely permits nonequivalences, for example flat extension Z -> Q, so it is not just a restatement of coherent descent for an adjoint equivalence.

The prior Lean theorem's docstring still mentions a successive-slice cocycle, while its actual signature and the retained DAG proof require only the single-slice comparison. This mismatch is inherited and not silently promoted into a new claim. The item statement has not changed. I preserved the newer Q63 correction rather than restoring the stale long proof.



Repair review, 2026-10-21: the first retained attempt passed dry run at be1e5532c89, but added only one node. That does not answer the explicit minimum of two in this return, so I did not push it. I separated its two substantive localization arguments and reran four kinds of search plus a second semantic phrasing for each revised statement. Neither new node cites the other, so two workers can take them independently. The normalization theorem now explicitly writes the localized unit map and all three coherence equations. The braiding theorem repeats the setting and normalization square and states the native braiding normalization on K-flat pairs, so it can be read independently. Its task includes verifying the signed complex comparison and descending its square to arbitrary unbounded derived objects; it is not an elementary consequence of the monoidal theorem (which assumes no symmetry of F).

Every part of the older long proof remains assigned: resolution/exact equivalence transport is Steps 1-2; native derived tensor normalization is the two new nodes; the K-injective closed adjunction and its representative counit are lem-sf-ringed-derived-tensor-hom-adjunction; the closed comparison and evaluation are lem-sfb-closed-scalar-hom-comparison; the actual native local module category and section/restriction comparison are def-sfb-internal-slice-derived-hom-comparison plus Step 5; normalized slice data and their evaluation are lem-weil-pbc-ringed-slice-normalized-comparisons and lem-weil-pbc-ringed-slice-evaluation-coherence; full-faithful conjugation is written in Step 6. Making further nodes for these existing statements would be duplicates. The old successive-slice cocycle assertion was already removed by the newer live review because it is not in the item's statement. I retain that correction.

For the new unit formula I checked the composite starts at E(1_D(C)) and ends at 1_D(D), with kappa at the degree-zero source unit between those endpoints. In the associator equation both sides start at E((K tensor L) tensor M) and end at EK tensor (EL tensor EM). In the new braiding equation both sides start at E(K tensor L) and end at EL tensor EK. Identity functors, zero complexes, the degree-zero unit and odd-degree rank-one complexes give the expected identities and signs; characteristic two and the zero ring remain admitted. All of the parent hypotheses are preserved byte for byte. The flat-cover transport supplies the internal functorial flat resolutions required in the existing derived-monoidal framework; no functorial choice of arbitrary resolutions is added to the item's hypotheses.

## Not duplicates

lem-sfb-exact-tensor-functor-derived-normalization vs def-zl-ringed-derived-closed-symmetric-monoidal-data: defines representative coherence data for one ringed category without asserting functorial coherence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-amb-derived-tensor-symmetry-involutive: proves the square of symmetry is identity in one etale derived category, with no exact comparison functor.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-coef-tower-natural-currying: curries a particular dualizing-tower pairing; it has no abstract normalized exact tensor functor assertion.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-per-proper-potential-bidual-comparison: is a proper direct-image/dualizing biduality comparison, not exact tensor functor normalization.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pur-finite-projection-action-laws: gives action identities for counit-defined projection maps, not normalized derived tensor-functor coherence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pur-projection-formula-coefficient-coherence: assumes a canonical strong monoidal pullback and proves projection-map identities; it does not supply that structure for an internal-section equivalence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pur-shifted-tensor-morphism-calculus: gives shift and homogeneous tensor identities for ringed-topos pullback, not generic exact-functor monoidal descent.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pur-system-primitive-comparison-shift: is shift compatibility for specified semilinear-system transformations, not the derived comparison for a general exact monoidal functor.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sf-etale-twisted-bidual-transport: transports a biduality map assuming evaluation-compatible comparisons, rather than proving derived tensor coherence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sf-ringed-derived-closed-symmetric-monoidal: constructs the closed symmetric structure of one ringed module category; it has no exact comparison functor between two categories.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sf-ringed-derived-native-tensor: identifies tensor localization constraints within one ringed module category; it does not identify E between independently fixed derived structures.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sf-ringed-rhom-derived-complete: closure of locally derived-complete objects under internal Hom, not derived tensor functor coherence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sf-ringed-tensor-complex-constraints: gives pure-generator formulas for constraints within one cochain category, with no derived comparison functor.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sfb-derived-internal-hom-sections-model: identifies a right adjoint with a sheaf-Hom complex and global Hom, not tensor-functor coherence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sfb-ringed-derived-monoidal-comparisons: treats pullbacks of specified ringed-topos morphisms and their compositions; no such morphism presents the internal-to-section-action equivalence.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sfb-ringed-derived-tensor-diagrams: requires a scalar-extension RingedTensorEdge between ringed-site presentations; the generic exact functor may start in an internal module-object category.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sfb-ringed-derived-tensor-lift: constructs a monoidal lift for a ringed scalar-extension edge, not for an arbitrary exact monoidal left adjoint preserving K-flat complexes.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-weil-proetale-derived-restriction-closed-monoidal: is specific to geometric weakly-etale restriction of A-valued sheaves and adds a closed comparison; the internal-to-section-action equivalence is not that restriction.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-wf-constant-twist-coefficient-comparison: identifies a particular Weil constant twist and Frobenius action, not the abstract derived tensor constraint maps.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-zl-contractible-derived-sections-tensor: is a sections theorem requiring a weakly-contractible or extremally disconnected base, absent for an arbitrary module-object comparison.

lem-sfb-exact-tensor-functor-derived-normalization vs prop-base-linear: is the Fourier transform base-linearity formula, not an exact tensor localization theorem.

lem-sfb-exact-tensor-functor-derived-normalization vs new-lem-kun-exact-monoidal-equivalence-derived: requires an adjoint equivalence and proves monoidal descent, including both adjoints and their units/counits; it does not assert the native Koszul braiding equation, and it does not cover nonequivalence F.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pur-derived-tensor-comparison: supplies the normalized natural morphism; it does not assert invertibility, associator/unit equations or compatibility with the native braidings.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pe-internal-section-tensor-comparison: is the underived section-action equivalence, total tensor and K-flatness comparison, not coherence for the independently fixed derived tensor.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-pd-module-ringed-topos-derived-comparison: concerns condensed coefficients on separated finite-type schemes in the standing positive-characteristic field setting and geometric pushpull/projection comparisons; it is not an abstract normalized exact tensor functor theorem and cannot apply to this unrestricted X or arbitrary slice site.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sc-standard-derived-equivalence-monoidal: concerns one universe-changing scheme derived equivalence and existence of CoreMonoidal only, not normalized maps or braided compatibility.

lem-sfb-exact-tensor-functor-derived-normalization vs lem-sfb-exact-tensor-functor-derived-braiding: the first proves invertibility and associator/unit equations without assuming F preserves symmetry; the second proves the native signed-braiding square, assuming the ordinary symmetry equation and a normalized t, without proving monoidal coherence. They are independent proof tasks.

lem-sfb-exact-tensor-functor-derived-braiding vs def-zl-ringed-derived-closed-symmetric-monoidal-data: defines representative coherence data for one ringed category without asserting functorial coherence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-amb-derived-tensor-symmetry-involutive: proves the square of symmetry is identity in one etale derived category, with no exact comparison functor.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-coef-tower-natural-currying: curries a particular dualizing-tower pairing; it has no abstract normalized exact tensor functor assertion.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-per-proper-potential-bidual-comparison: is a proper direct-image/dualizing biduality comparison, not exact tensor functor normalization.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pur-finite-projection-action-laws: gives action identities for counit-defined projection maps, not normalized derived tensor-functor coherence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pur-projection-formula-coefficient-coherence: assumes a canonical strong monoidal pullback and proves projection-map identities; it does not supply that structure for an internal-section equivalence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pur-shifted-tensor-morphism-calculus: gives shift and homogeneous tensor identities for ringed-topos pullback, not generic exact-functor monoidal descent.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pur-system-primitive-comparison-shift: is shift compatibility for specified semilinear-system transformations, not the derived comparison for a general exact monoidal functor.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sf-etale-twisted-bidual-transport: transports a biduality map assuming evaluation-compatible comparisons, rather than proving derived tensor coherence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sf-ringed-derived-closed-symmetric-monoidal: constructs the closed symmetric structure of one ringed module category; it has no exact comparison functor between two categories.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sf-ringed-derived-native-tensor: identifies tensor localization constraints within one ringed module category; it does not identify E between independently fixed derived structures.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sf-ringed-rhom-derived-complete: closure of locally derived-complete objects under internal Hom, not derived tensor functor coherence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sf-ringed-tensor-complex-constraints: gives pure-generator formulas for constraints within one cochain category, with no derived comparison functor.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sfb-derived-internal-hom-sections-model: identifies a right adjoint with a sheaf-Hom complex and global Hom, not tensor-functor coherence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sfb-ringed-derived-monoidal-comparisons: treats pullbacks of specified ringed-topos morphisms and their compositions; no such morphism presents the internal-to-section-action equivalence.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sfb-ringed-derived-tensor-diagrams: requires a scalar-extension RingedTensorEdge between ringed-site presentations; the generic exact functor may start in an internal module-object category.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sfb-ringed-derived-tensor-lift: constructs a monoidal lift for a ringed scalar-extension edge, not for an arbitrary exact monoidal left adjoint preserving K-flat complexes.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-weil-proetale-derived-restriction-closed-monoidal: is specific to geometric weakly-etale restriction of A-valued sheaves and adds a closed comparison; the internal-to-section-action equivalence is not that restriction.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-wf-constant-twist-coefficient-comparison: identifies a particular Weil constant twist and Frobenius action, not the abstract derived tensor constraint maps.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-zl-contractible-derived-sections-tensor: is a sections theorem requiring a weakly-contractible or extremally disconnected base, absent for an arbitrary module-object comparison.

lem-sfb-exact-tensor-functor-derived-braiding vs prop-base-linear: is the Fourier transform base-linearity formula, not an exact tensor localization theorem.

lem-sfb-exact-tensor-functor-derived-braiding vs new-lem-kun-exact-monoidal-equivalence-derived: requires an adjoint equivalence and proves monoidal descent, including both adjoints and their units/counits; it does not assert the native Koszul braiding equation, and it does not cover nonequivalence F.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pur-derived-tensor-comparison: supplies the normalized natural morphism; it does not assert invertibility, associator/unit equations or compatibility with the native braidings.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pe-internal-section-tensor-comparison: is the underived section-action equivalence, total tensor and K-flatness comparison, not coherence for the independently fixed derived tensor.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-pd-module-ringed-topos-derived-comparison: concerns condensed coefficients on separated finite-type schemes in the standing positive-characteristic field setting and geometric pushpull/projection comparisons; it is not an abstract normalized exact tensor functor theorem and cannot apply to this unrestricted X or arbitrary slice site.

lem-sfb-exact-tensor-functor-derived-braiding vs lem-sc-standard-derived-equivalence-monoidal: concerns one universe-changing scheme derived equivalence and existence of CoreMonoidal only, not normalized maps or braided compatibility.

## What remains

Both new nodes are intentionally statement-only for separate future stage-1 workers. No part of this assignment is left unfinished; the required server dry run and direct push complete the delivery.

## Validation

Initial server deliver.py --no-push returned OK at 116d084988e. A final notation cleanup renamed the flat-cover functor C so it does not shadow the native tensor T. The dry run is repeated on the final files before direct delivery.
