# Worker report

1. Files written:
   - `dag/nodes/sec-deligne-laumon-general/lem-zl-compact-support-leray-filtration.json`: item split; statement unchanged; no Mathlib match.
   - `dag/nodes/sec-deligne-laumon-general/lem-zl-field-shriek-lower-bound.json`: new statement-only unsplit lemma, no Mathlib match.
   - `dag/nodes/sec-deligne-laumon-general/lem-zl-field-shriek-composition-qcqs.json`: new statement-only unsplit lemma, no Mathlib match.
   - `citations.json`: verbatim statement quotations for all step citations.
2. Attachments: none. Read `WeilConjectures/DeligneLaumon/Reduction/FormalSteps.lean` lines 89–130. `AlgebraicGeometry.WeilSheaf.exists_filtration_higherLowerShriek_comp` ends in `sorry`; moreover its concrete AdicSheaf Weil category is not the item's common-stage category. Searches by item id, Leray, compact-support filtration and the operation names found no exact closed project declaration.
3. WANTED: none. The mathematical sources used are available locally. The two new field-coefficient lemmas remain explicit proof obligations; their sources identify the finite-level/complete constructions, not already-written proofs of the extra field statements.
4. Faults corrected: the imported item had no proof. The ancestor blueprint cites `def-weil-pbc-hypercohomology-filtrations` and `lemma-weil-pbc-hypercohomology-convergence` for arbitrary compact-support field coefficients, but their actual statements cover ordinary direct images of torsion abelian étale complexes in a base-change square. They are not applicable here. Also `lem-zl-shriek-composition` and `prop-functor-package` require separated structure morphisms for the schemes, which the item does not assume. Neither reference was used to smuggle in those stronger hypotheses. The original common-stage formulation and all its nonseparated cases are retained. The replacement constructs exactly the same truncation spectral sequence and uses general exact-couple convergence, so it retains the unit route. The category of Weil pairs is never treated as triangulated.
5. Remaining work: proofs of the two statement-only lower-level interfaces are future DAG items. The current item is completely split by one level. No Lean file was changed or compiler invoked; only the sandbox was written.

## Blueprint and searches

Read the chapter `sec-deligne-laumon-general`, unit `sk-l-dl-general-composition`, current main-20261015 ancestor proof, and the current composition proof. This child is not the unit key statement, so no unit realization file was changed. Ancestor query returns `lem-zl-composition-weight-bound`; new-node ancestry includes this item in `via`. Whole-blueprint searches for Leray, compact support, composition, triangulated, lower cohomological bound, 0F7J and 0G2A found no exact replacement for either new field-coefficient statement. Whole-DAG searches by notion and by tags were also read. Both new nodes are smaller tools about the operation itself, not a clause or renamed version of the requested filtration.

All new search entries came from the required msearch.py command; searches.jsonl records their exact tools and queries. Lower-bound searches were tried as nonnegative cohomology and as preservation of a lower bound by a triangulated functor; composition searches as compact-support composition and pseudofunctor common-stage composition; the item as Leray filtration and hypercohomology of a Weil complex. LeanSearch, LeanFinder, Loogle and source grep ran. Hits concerned ordinary scheme module pushforwards, derived-category cohomological support, compactly supported functions or spectral-object input data; none states either new adic operation interface or the item. Read the Mathlib TStructure Heart/SpectralObject files and the spectral-object input description: these do not construct this particular compact-support couple. The general t-structure cohomological theorem already has the DAG node `lem-weil-heart-short-exact-triangles`, so no extra node for it was created. The item retains its historical searches and appends this session's searches.

## Review by Q54

I read the ancestor's first paragraph and its second paragraph through the filtration assertion, Stacks `more-etale.tex` Tag 0F7J (`lemma-shriek-composition`) and Tag 0G2A (`lemma-derived-lower-shriek-bounded`, especially part (3)), Bhatt–Scholze Definition 6.7.6, Lemma 6.7.7 and the open-extension discussion 6.1.11–6.1.13, and BBD 1.3.3–1.3.6 (especially the heart/cohomological-functor theorem 1.3.6). I also read Stacks `homology.tex` exact couples 011Q, 011R, 011S and its cycle/boundary description. The field-coefficient extensions of the compactification formula are not attributed directly to a theorem about discrete non-torsion étale coefficients. They are what the two new unsplit nodes explicitly ask to prove. Neither node includes a proof sketch in place of a statement.

For the new lower-bound lemma, I checked that the input is a bounded constructible object of the rationalized or common-stage category, not an arbitrary finite-level reduction of a rational object. Its conclusion preserves the same lower cohomological bound and asserts triangulated exactness; it does not assert exactness on sheaves or vanishing of positive higher images. At the finite model 0G2A supplies exactly the lower endpoint; Bhatt–Scholze supplies the completed compactification construction and constructibility on qcqs schemes. The scalar-stage passage is an explicit remaining obligation. This is not the existing finite-coefficient triangulated lemma or finite constructibility theorem. For the new composition lemma I checked both arrows are separated finite type, all three schemes are quasi-separated finite type, and coefficients are those actually used by the item. Its specified map is the compatible compactification proper/open map, not an arbitrary isomorphism of output objects. 0F7J constructs that finite comparison; the field-stage version is the new obligation. The old `lem-zl-shriek-composition` would only handle separated schemes, and finite/tower versions do not immediately assert this field-stage interface.

Step 1 uses the actual abelian constructible-heart statement, the exact automorphism compatibility of `prop-constructible-truncations`, and the fixed-pair definition of Weil sheaves. I wrote out kernels and cokernels in the fixed heart by their universal properties; no triangulated structure on fixed pairs is assumed. This is an elementary abelian-category construction, not an unproved assertion about a derived category of Weil sheaves.

Step 2 uses the new lower-bound node for bounded constructibility and absence of negative cohomology of Rh_!F, and its triangulated assertion for T=Rg_!. `lem-fix-weil-operations` gives their Weil structures on precisely these bounded constructible domains. I added explicit citations for finite-type composition/base change, separated finite-type base change, and qcqs source/base-change permanence after noticing these hypothesis checks should not be left implicit. Their statements, including arbitrary base change, were opened and copied to citations.json. In particular X is not silently assumed separated over the base field.

Step 3 uses `prop-constructible-truncations` for the actual standard bounded t-structure and automorphism comparison, `lem-weil-heart-short-exact-triangles` for truncations and its clause (5) for the long exact sequence, the new functor exactness, and `def-sp-exact-couple` for the precise three exactness equalities and bidegrees. Taking the canonical truncation triangle of the truncated object identifies its third term with H^b(K)[-b]. Every D, E and boundary is formed in the underlying common-stage triangulated category before passing to its Weil heart. Naturality gives the Frobenius-compatible boundaries. This is the explicit construction missing from the imported item, not an invocation of the ordinary-étale specialization.

Step 4 uses the shift and lower-bound clauses of the new node to compute E_2 and prove both quadrant vanishings. `lem-sp-derived-couple-exact` clause (4) states the iterative page formula and bidegree used. No mere definition is cited for the theorem that the derived couples remain exact.

Step 5 applies `thm-sp-half-plane-convergence` only after checking both its D and E support hypotheses with lower bound zero. Its statement gives the finite image filtration and the infinite-page graded isomorphism. I independently checked the actual abutment: the third term T(tau>=n+1 K) has zero H^(n-1) and H^n, so the cited long exact sequence makes c_n an isomorphism. The filtration then transports to H^n(TK); no colimit over a large category is needed. The canonical filtration is in the Weil heart because the exact couple is there.

Step 6 uses `def-sp-convergence` for the initial-page cycle and boundary subobjects, and convergence for stabilization by n+2. S is the actual stabilized cycle subobject of E_2, and its map onto the stabilized quotient is epi. Thus the required subquotient has a single monic presentation in the original E_2 term; no unstated transitivity lemma about subquotients is hidden here. This is an elementary extraction from the two cited statements.

Step 7 uses the new composition comparison, then precisely the composition-equivariance clause of `lem-fix-weil-operations`. I checked the indices with j=1 and j=n+1: they give (a,b)=(n,0) and (0,n), and G_0=F^(n+1)=0, G_(n+1)=F^0=H^n. The graded quotient uses F^a/F^(a+1), so the increasing reindexing has the correct orientation. No mixedness or weight assumption appears anywhere.

Edge cases checked: n=0 gives one step with the (0,0) term; a zero sheaf or empty source gives a chain of zero objects with valid mono/epi maps; identity h or g yields the expected degenerate filtration. The new lower-bound lemma allows every integer c and does not assert an upper vanishing bound. Proper maps reduce to ordinary derived direct images, and open maps are compatible with the compactification formula. Nonseparated finite-type schemes (for example a doubled-origin base with the identity maps) remain allowed; no global separatedness is added. All proof steps are below 2000 characters and none hides a comparison lemma: the two nontrivial operation interfaces are separately stated nodes. Every cited statement was opened and every citations.json quote checked as a verbatim substring. B1–B10, C1–C8, D1–D5 and E1–E7 were checked against these files and the sources, including statement-only new leaves, correct coefficient domains, no cycles, no hollow definitions, and no SGA source. Tool uses are declared in split_report rather than setting the maintainer-owned tool_uses field.

## Not duplicates

lem-zl-field-shriek-lower-bound vs lem-pur-bounded-heart-amplitude: the existing lemma assumes a heart-amplitude bound for an exact functor on ordinary derived categories; it does not prove that bound for the adic compact-support functor.

lem-zl-field-shriek-lower-bound vs prop-finite-compact-support-constructibility: the existing statement concerns Finite-level bounded constructibility for proper support; it does not assert the field-coefficient lower-bound and exactness interface for Rf_! on all bounded constructible common-stage inputs.

lem-zl-field-shriek-lower-bound vs sk-lem-geo-finite-boundary: the existing statement concerns Detection by a proper direct image; it does not assert the field-coefficient lower-bound and exactness interface for Rf_! on all bounded constructible common-stage inputs.

lem-zl-field-shriek-lower-bound vs sk-lem-geo-smooth-generic: the existing statement concerns Smooth morphisms and locally constant sheaves; it does not assert the field-coefficient lower-bound and exactness interface for Rf_! on all bounded constructible common-stage inputs.

lem-zl-field-shriek-composition-qcqs vs cor-amb-affine-space-adjunction: the existing statement concerns Affine-space ambient adjunction; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs fix-lem-exchanges: the existing statement concerns Exchange functoriality: naturality, identities, and pasting; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-amb-etale-adjoint-locality: the existing statement concerns Etale localization of the ambient adjoint; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-amb-etale-compact-comparisons: the existing statement concerns The etale compact-support comparisons; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-amb-shriek-open-exchange-adjoint: the existing statement concerns Open compact-support exchange is the extension-composition mate; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-amb-shriek-tensor-composition: the existing statement concerns Tensor projection maps respect compact-support composition; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-amb-unbounded-compact-support-comparisons: the existing statement concerns Unbounded ordinary etale compact-support comparisons; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-cbc-compactifiable-compatible-tower: the existing statement concerns Compatible compactification towers with a supplied compactification of the composite; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-cbc-complete-proetale-composition-pasting-coherence: the existing comparison is on constant-ring strict towers with finite-coefficient evaluations and a supplied compatible tower; the new node asserts the comparison after completed integral and rational/common-stage passage on Db_c.

lem-zl-field-shriek-composition-qcqs vs lem-pur-finite-adjoint-mate-compatibility: the existing statement concerns Finite reduction preserves the canonical adjoint mates; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-pur-projection-purity-agreement: the existing statement concerns Agreement with the affine-line route on affine space; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-pur-system-compactification-pf-substitution: the existing statement concerns Refinement comparisons intertwine strict-system projection maps; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-pur-system-level-projection-formula-coherence: the existing statement concerns Strict-system projection formula composition coherence; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sf-compact-coefficient-composition: the existing statement concerns Finite coefficient comparison respects compact-support composition; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sf-composition-projection-mate: the existing statement concerns Normalized compact-support composition satisfies the projection mate identity; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sf-kunneth-coherence: the existing statement concerns Coherence of the relative product; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sf-product-compactification-identity: the existing statement concerns Product compactification identity for the exchange/projection composite; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sf-unbounded-compact-support-proper-composition: the existing statement concerns Unbounded ordinary etale compact supports composed with a proper direct image; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sfb-proper-open-tower-derived-unit: the existing statement concerns Derived-unit resolution calculation in a proper/open tower; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sfb-quasifinite-compact-support-exact: the existing statement concerns Quasi-finite compact support is exact and agrees with compactifications; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sp-coefficient-tower-shriek-calculus: the existing statement concerns Compact-support calculus on varying coefficient towers; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-sp-compactification-refinement-coherence: the existing abstract compactification coherence theorem requires supplied proper/open functors and comparisons; the new node asserts the concrete field-coefficient comparison on the specified common-stage categories.

lem-zl-field-shriek-composition-qcqs vs lem-sp-et-proet-coefficient-compatibility: the existing statement concerns Finite coefficient compact-support comparison respects site transport, refinement and composition; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-compact-composition-proper-square-normalization: the existing statement concerns Compact-support composition along a proper square: closed and open normalizations; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-compact-composition-tower-formula: the existing statement concerns Computing finite pro-etale compact-support composition on a compatible tower; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-compact-support-exchange-counit: the existing statement concerns Compact-support exchange intertwines proper ordinary counits; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-filtered-derived-operation-lifts: the existing statement concerns Filtered lifts of sheaf-derived operations and their canonical adjunction maps; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-finite-horizontal-shriek-mate: the existing statement concerns Compact-support exchange as a mate along finite horizontal arrows; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-finite-structural-maps-commshift: the existing statement concerns Canonical finite-coefficient structural maps commute with shifts; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-proper-compact-unit-reduction: the existing statement concerns Finite reduction of the proper compact-cohomology unit; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-proper-composition-site-transport: the existing statement concerns Site comparison preserves compact-support composition with a proper factor; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-proper-specialization-borel-moore-compatibility: the existing statement concerns Borel–Moore specialization commutes with proper pushforward of lifts; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-trf-proper-unit-localization-composition: the existing statement concerns Proper-endomorphism units commute with open and closed compact-support composition; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-delta-proper-pushforward: the existing statement concerns The double-dual morphism under a proper push-forward; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-pbc-compatible-compactification-triangle: the existing statement concerns Compatible geometric compactifications of a composable pair; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-pbc-etale-compact-support-open-closed-triangle: the existing statement concerns Open-closed localization for relative etale compact support; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-pbc-etale-lisse-open-relative-line-constructibility: the existing statement concerns Lisse coefficients on an open relative affine line over an integer model; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-pbc-etale-shriek-qcqs-composition: the existing statement concerns Composition of qcqs etale compact-support candidates; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-weil-pbc-etale-shriek-relative-mayer-vietoris: the existing statement concerns Relative Mayer Vietoris for qcqs etale compact support; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs prop-asd-smooth-base-change: the existing statement concerns Arbitrary base change for smooth ambient duality; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs sk-lem-geo-affine-local: the existing statement concerns Affine space and étale localization; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs sk-thm-sf-verdier-exchange: the existing statement concerns Verdier-duality exchange; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-amb-vector-bundle-purity: the existing statement concerns Vector-bundle purity before smooth orientation; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-asd-smooth-tensor: the existing statement concerns Smooth cohomological duality without a chosen orientation; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-cbc-complete-proetale: the existing statement concerns Complete pro-etale compact-support base change; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-cbc-finite-torsion: the existing statement concerns Compact-support base change at finite coefficients; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-sf-comp-composition: the existing statement concerns The composition law for $Rf_!$; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs thm-weil-etale-geometric-biduality: the existing statement concerns Finite-stage etale Verdier biduality; it does not assert the concrete common-stage field-coefficient compact-support composition for arbitrary separated maps of possibly nonseparated finite-type schemes.

lem-zl-field-shriek-composition-qcqs vs lem-zl-shriek-composition: the existing field comparison assumes the schemes are separated over k_0; the new statement retains only separatedness of the two morphisms, as the item requires.

lem-zl-field-shriek-composition-qcqs vs prop-functor-package: the package assumes separated schemes; the new interface covers quasi-separated finite-type schemes without that extra hypothesis.

lem-zl-field-shriek-lower-bound vs lem-compact-support-direct-image-triangulated: the existing exactness theorem is at finite coefficient A_(E,n), with no field-stage lower-bound clause.

lem-zl-field-shriek-lower-bound vs lem-sf-constructible-exceptional-adjunction-coefficients: the existing adjunction interface gives exact functors on its finite-Tor categories but no preservation of the standard lower cohomological bound.
