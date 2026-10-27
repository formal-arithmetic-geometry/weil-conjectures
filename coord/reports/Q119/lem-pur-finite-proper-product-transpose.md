## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-finite-proper-product-transpose.json`: retained statement and Lean record; replaced the returned seven-step proof with a five-step assembly of 2312 characters.
- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-derived-product-leg-transposes.json`: statement, unsplit; no Mathlib match. Extracts the two input-leg calculations, including both signed symmetries.
- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-derived-composite-transpose.json`: statement, unsplit; no Mathlib match. Extracts successive transposes for arbitrary arrows through the specified finite K-injective compositor.
- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-derived-isomorphism-transport-transpose.json`: statement, unsplit; no Mathlib match. Extracts the isomorphism-transport comparison and its transpose for arbitrary arrows and coefficient isomorphisms.
- `citations.json` and `report.md`; local preparation/search artifacts are not delivery files.

There are **3 new nodes, 0 Mathlib leaves**. Every new node is statement-only: `proof=[]`, `proof_deps=[]`, `proof_origin=null`, `status=unsplit`. No Lean was written, no compiler or Lake tool was run, and nothing in the read-only repository or launcher was changed.

Attachments: none. The exact blueprint tag has no match in `lean/WeilConjectures`. The declaration `WeilConjectures.FiniteProperProduct.finiteProperProductTranspose` in `lean/Sheaf/Paper/FiniteProperProductTranspose.lean` has a final `sorry`. The pro-etale `SixFunctors/ProEtale/FiniteCoefficient/Derived/ExternalProduct.lean` defines the external-product object; the etale `SixFunctors/Etale/Derived/Kunneth/Relative.lean` assembly theorem proves existence of a different isomorphism, rather than these specified ordinary pro-etale arrow identities. None is an attachment of this item or of the three extracted lemmas.

WANTED: none.

This repairs the 2026-10-22 batch5 re-split return, not an unchanged re-push. The sandbox initially contained only `.brief*`; there was no retained node, report, citations file or search log to reuse. I copied the current live item, retained every field except its split-owned proof/report fields, and saved the previous N0 report as `previous-report.md`. The current item includes its merged stage-2 Lean record; that record, the statement, dependencies of the statement, all old Mathlib searches and provenance remain unchanged. The complete old proof is reproduced below, so every previous argument remains available to the workers and independent reviewer. There is no statement dispute. No unit or chapter route was changed.

## Repair of the re-split return

The 5519-character proof is divided by argument, rather than summarized:

1. Original Steps 2--3 go to the product-leg lemma. Its statement includes the actual source comparisons, the exchange map, both projection maps, both signed symmetries and both transpose identities. Its assigned argument is 1341 characters in the original proof.
2. Original Steps 1 and 4 go to the composite-transpose lemma. It uses the already existing normalized-comparison theorem, rather than proposing a second theorem asserting only counit normalization. Its additional claim concerns arbitrary input arrows `w` and `v` through the specified pro-etale compositor and compares both Hom bijections. Its assigned argument is 1702 characters.
3. Original Step 6 goes to the isomorphism-transport lemma. It states an actual formula for transport, asserts it is the canonical isomorphism, and computes the transpose for arbitrary `u` and `d`. Its assigned argument is 1059 characters.
4. Original Steps 5 and 7 remain the short assembly: tensor bifunctoriality composes the two counits; signed-symmetry naturality and involution prove the swap. The new item also explicitly applies each extracted statement with its objects and maps. No one new node states the whole item, and none of the new statements contains a proof sketch.

The three extracted tasks have comparable original argument sizes. The assembly is below 3000 characters, and each of its steps is below 2000. The three new statement-only nodes have no long proof step to inspect. The return specifically asks for independently assignable arguments even where the old proof called a calculation elementary; the extraction preserves the actual derived operations and their normalization, rather than creating nodes for a bare symmetry-involution or tensor-bifunctor law.

## Sources and searches

I read Stacks `sites-cohomology.tex`, Tag 0E48, label `remark-compatible-with-diagram`, and the preceding `equation-projection-formula-map`; also `lemma-adjoint`, and Tag 0D6E, `lemma-derived-pushforward-composition`, with their proofs. These are the sources for the maps and composition, not literal assertions of all our new comparisons: the new nodes are explicitly agent-formulated calculations from them. I read the current `main-20261015` blueprint `sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`, especially the proper two-counit paragraph, and `sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`, Steps 3--4. Its proper-product ingredient is the route we retain. The older ancestry/unit ids are preserved as the live DAG records them.

The leg node is sourced at 0E48 and the projection-map equation. The composite and transport nodes are sourced at 0D6E, with the respective explicit agent-calculation attribution. None cites SGA or imports exceptional/compact-support machinery. The blueprint's phrase 'inverse to the transpose' is not used to invert an exchange or projection map: on these unrestricted objects the forward product is the adjoint of the tensor of counits.

Whole-DAG searches used the exact tag, transpose/counit/compositor/transport keywords, and the prospective ids. Whole-blueprint searches were run with `tools/blueprint_refs.py search` for `successive transposes`, `transported transpose`, `symmetrized projection`, and `tensor of the two pulled back counits`; each exact search returned zero blueprint nodes. Broader searches for projection/exchange, transport/adjunction and 0E48 supplied candidate nodes; the relevant statements were opened, including both ringed Kunneth/comparison lemmas, the ringed monoidal theorem, derived-composition normalization, ringed exchange/tensor coherence, projection exactness, and adjoint-square transport. The ancestry command names `prop-pur-affine-space-composition-law`; the `from.place` and `via` fields identify the proper-product paragraph through the live ancestors.

Each new node has searches actually run by the prescribed `msearch.py`, with the exact tool/query and results retained. Each received LeanFinder, LeanSearch, Loogle and grep, and a second semantic phrasing. All services answered. The first leg Loogle query had an unknown qualified braiding identifier; the corrected query is separately recorded, with no fabricated hits. Read Mathlib candidates include `Adjunction.comp_homEquiv` and `comp_counit_app` (`CategoryTheory/Adjunction/Basic.lean:580,584`), `SheafOfModules.conjugateEquiv_pullbackComp_inv` (`Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:177`), `Scheme.Modules.conjugateEquiv_pullbackComp_inv` (`AlgebraicGeometry/Modules/Sheaf.lean:265`), `Adjunction.derivedε_fac_app` (`CategoryTheory/Functor/Derived/Adjunction.lean:125`) and the triangle/naturality API. The abstract composite Hom bijection does not itself normalize the specified derived pro-etale compositor; the sheaf/module conjugacy results are underived. Slice-category pullbacks and coalgebra counits do not state our tensor-mate identities. No candidate supplies a one-line specialization of a whole extracted statement.

## Not duplicates

lem-pur-ordinary-derived-product-leg-transposes vs lem-sbc-strict-perfect-tower-projection: the existing statement is Local perfectness and invertibility of the strict tower projection (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs def-sbc-quotient-exchange-scalar-comparisons: the existing statement is Quotient specialization and scalar comparison equation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs def-sbc-strict-augmented-coefficient-presentation: the existing statement is Normalized strict augmented coefficient square presentation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sbc-strict-reduction-pullback-square: the existing statement is The normalized coefficient reduction square before taking mates (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sbc-strict-projection-coaugmentation: the existing statement is Strict coefficient projection and the normalized limit coaugmentation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs def-sbc-quotient-coefficient-presentation: the existing statement is Quotient coefficient presentations and exact derived scalar restriction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sbc-strict-tower-mate-evaluation: the existing statement is Normalized evaluation of the actual strict tower square mate (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sbc-strict-quotient-exchange-unit-equation: the existing statement is Coaugmentation equation for the strict perfect-coefficient exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs def-sbc-strict-coefficient-exchange-arrows: the existing statement is Canonical strict coefficient exchange arrows and evaluation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sf-constant-semilinear-generator-comparison: the existing statement is Scalar restriction identifies the single proper and open reduction generators (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sf-generator-reduction-coherence: the existing statement is Basic generator coefficient squares in semilinear systems (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-completed-reduction-pullback-square: the existing statement is Completed reduction respects the strict inverse-image square (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-ringed-square-tensor-compatibility: the existing statement is Tensor compatibility of a ringed square on flat K-flat representatives (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing theorem states equality of two exchange/projection naturality composites, not the pair of leg transposes nor the arbitrary-arrow transport identity.

lem-pur-ordinary-derived-product-leg-transposes vs lemma-weil-pbc-completed-exchange-coherence: the existing statement is Completed exchange coherence (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing statement is Finite reduction and the canonical pullback square (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-finite-reduction-pullback-square: the existing statement is Finite reduction respects the inverse-image square (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement is Coefficient normalization of the raw ordered completed exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-finite-level-rectangle: the existing statement is Finite-level exchange rectangle (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-completed-exchange-unit: the existing statement is Completed exchange extends the ordinary mate along its unit (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs def-weil-pbc-ringed-tensor-square-presentation: the existing statement is Representative presentation of a commutative ringed tensor square (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-flat-scalar-tower-exchange: the existing statement is Flat scalar restriction transports the strict-diagram adjunction mate (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the existing statement is Finite exchange rectangle for intrinsic coefficient reduction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-pur-projection-comparison-etale-origin: the existing statement is Etale-origin comparison intertwines compact-support projection maps (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sp-categorical-projection-mate-square: the existing statement is Tensor-compatible adjunction squares preserve projection maps (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sp-compact-projection-base-change: the existing statement is Compact-support projection map commutes with base change (finite rings and coefficient towers) (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-pur-finite-proper-product-transpose: the item additionally assembles the two counits into Omega and proves product-swap symmetry; the extracted statement is strictly smaller and independent of those final claims.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sp-completion-mate-comparison: the existing statement is The strict quotient-tower exchange realizes the completed-adjunction mate (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-amb-shriek-tensor-composition: the existing statement is Tensor projection maps respect compact-support composition (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-amb-compactification-projection-composition: the existing statement is Projection maps respect the explicit proper/open compactification tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-amb-shriek-projection-open-restriction: the existing statement is Compact-support projection maps commute with open base restriction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-pur-co-smooth-pf-exchange-coherence: the existing statement is Projection/exchange coherence for compact support (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-fix-etale-origin-scalar-projection-square: the existing statement is The scalar restriction of the etale-origin projection square for a qcqs morphism (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-pur-finite-forward-product-symmetry: the existing statement is Symmetry of the finite forward compact-support external product (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes both ordinary constant-A exchange/projection leg transposes, with the two signed projection symmetries.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sfb-ringed-derived-monoidal-comparisons: the existing theorem normalizes functor comparisons, counits and 2-isomorphisms, but does not state the displayed arbitrary-arrow composite or isomorphism-transport transpose calculation.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sfb-derived-composition-adjunction-normalization: the existing theorem constructs the normalized K-injective composition comparison; it does not state the displayed arbitrary-arrow successive-transpose formula.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sfb-ringed-kunneth-factorizations: the existing theorem treats two endomorphism paths over one map q with inputs on the same source X, rather than the separate leg identities or arbitrary composable-arrow and isomorphism-transport formulas.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sfb-ringed-comparison-tensor-adjunction: the existing theorem compares two ringed paths and their monoidality/conjugacy, without the displayed two-leg or unit-insertion transport calculation.

lem-pur-ordinary-derived-product-leg-transposes vs lem-weil-derived-direct-image-composition: the existing theorem gives functor composition and coherence, without the stated arrow-level transpose identity.

lem-pur-ordinary-derived-product-leg-transposes vs lem-trf-exceptional-kunneth-counit: the existing theorem is for exceptional constructible finite-Tor adjunctions and the exceptional Kunneth map, not ordinary unbounded pullback/direct-image adjunctions.

lem-pur-ordinary-derived-product-leg-transposes vs lem-sf-kv-alpha-transpose-coherence: the existing theorem concerns exceptional Kunneth alpha composition and swap, not the ordinary unbounded exchange/projection legs or specified compositor calculus.

lem-pur-ordinary-derived-composite-transpose vs lem-coef-enriched-sequence-projection-formula: the existing statement is Uncurried finite projections of the enriched sequence adjunction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-coef-sequence-sections-limit-comparison: the existing statement is Derived sections and total limit with specified projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-coef-sequence-pushforward-limit-projections: the existing statement is Restricted total-limit comparison with adjunction projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-coef-sequence-global-sections-evaluation: the existing statement is Derived termwise global sections with finite evaluation and transition normalization (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-coef-derived-sections-scalar-coherence: the existing statement is Coherent unit-normalized scalar comparison for unbounded derived global sections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-trf-completion-unit-models: the existing statement is Ordinary quotient adjunction and normalized derived completion models (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-trf-completion-unit-canonical-models: the existing statement is Compatible ordinary and derived presentations of the coefficient adjunction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-proper-open-tower-single-unit-formula: the existing statement is Single derived-unit formula in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-proper-open-tower-successive-unit-formula: the existing statement is Successive derived-unit formula in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-proper-open-tower-derived-unit: the existing statement is Derived-unit resolution calculation in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-ringed-comparison-tensor-adjunction: the existing theorem compares two ringed paths and their monoidality/conjugacy, without the displayed two-leg or unit-insertion transport calculation.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-exact-compactification-unit-refinement: the existing statement is Normalized exact compactification units respect canonical refinements (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-integral-quotient-direct-image-comparison: the existing statement is Unbounded quotient-scalar refinement of integral direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-exact-compactification-unit-composition: the existing statement is Composition of normalized exact compact-support units (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-sfb-ringed-derived-comparison-data: the existing statement is Data of normalized derived monoidal comparisons of ringed topoi (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-ringed-kunneth-factorizations: the existing theorem treats two endomorphism paths over one map q with inputs on the same source X, rather than the separate leg identities or arbitrary composable-arrow and isomorphism-transport formulas.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-ringed-derived-composition-comparison: the existing statement is Composition comparison with normalized representative formulas (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-ringed-derived-identity-comparison: the existing statement is Identity comparison with normalized representative formulas (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-derived-composition-adjunction-normalization: the existing theorem constructs the normalized K-injective composition comparison; it does not state the displayed arbitrary-arrow successive-transpose formula.

lem-pur-ordinary-derived-composite-transpose vs lem-sfb-ringed-derived-monoidal-comparisons: the existing theorem normalizes functor comparisons, counits and 2-isomorphisms, but does not state the displayed arbitrary-arrow composite or isomorphism-transport transpose calculation.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing statement is Identity and pasting for ordinary ambient ringed exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing statement is Canonical composition comparison for unbounded ringed-topos direct images (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing statement is Derived adjunctions under compatible changes of ring sheaves (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-weil-pbc-derived-direct-image-composition: the existing statement is Composition isomorphisms of derived direct images (conjugates of those of inverse images) (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-weil-pbc-adjunction-conjugate: the existing statement is Conjugate transformations of adjoint functors (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-ring-sheaf-change-adjunction-existence: the existing statement is Existence of the normalized derived direct-image comparison (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-frobenius-exchange-restriction: the existing statement is Finite-level exchange is the restricted ambient exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-asd-proper-finite-coefficient-extension-core: the existing statement is Unbounded proper coefficient comparison and restricted projection identity (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-coefficient-projection-cocycle: the existing statement is Coefficient projection cocycle for ordinary derived ringed diagrams (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-coefficient-derived-presentation-exists: the existing statement is Existence of a normalized derived coefficient presentation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-pur-sequence-adjoint-resolution-data: the existing statement is Resolution data for the coefficient sequence projection (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sp-restriction-transition-transpose: the existing statement is Scalar-adjunction transpose of a compact-support mixed-coefficient map (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-cbc-strict-tower-direct-image-coherence: the existing statement is Coherence of canonical strict-tower direct image and its square mates (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-kun-module-abelian-kinjective-direct-image-acyclic: the existing statement is Abelian direct-image acyclicity of a module K-injective complex (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-completed-coefficient-site-data: the existing statement is Exact scalar restrictions, strict-system restriction and derived limit on one site (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-system-pushforward-restriction-transition: the existing statement is Restriction-form transition of simultaneous derived direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-sf-compact-support-restriction-of-scalars: the existing statement is Finite-level compact-support direct image commutes with restriction of scalars (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-completed-coefficient-structure-map: the existing statement is Unique completed coefficient structural map from finite projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-sequence-adjoint-resolution-shifts: the existing statement is Resolution-normalized identification of the sequence-site derived adjoints (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-derived-composition-cocycle: the existing statement is Cocycle and identity laws for normalized ringed-topos derived composition (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-coefficient-restriction-counit: the existing statement is Derived ringed-topos counit under coefficient restriction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-proetale-direct-image-global-evaluation: the existing statement is Normalized derived global sections after pro-etale direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-cbc-etale-derived-direct-image-coherence: the existing statement is Ordinary etale derived direct-image composition and its coherence (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-completed-coefficient-direct-image-diagrams: the existing statement is Normalized completed-coefficient direct image on strict diagrams (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-kun-etale-module-abelian-ringed-presentation: the existing statement is Simultaneous ringed presentations of coefficient forgetting and abelian etale direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-diagram-ring-restriction-pushforward: the existing statement is Derived coefficient restriction on ringed diagram topoi (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing statement is Inverse-limit acyclicity of levelwise pushforward of a K-injective tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-perfect-quotient-exchange-normalization: the existing statement is Perfect quotient coefficient exchange with augmentation and completion-unit normalization (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-pur-completed-pushforward-models: the existing statement is Normalized models for completed-coefficient direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-asd-proper-finite-coefficient-extension: the existing statement is Canonical unbounded proper direct-image comparison for finite coefficient extension (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-pur-ringed-coefficient-change-presentations: the existing statement is Normalized coefficient changes between counit presentations (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-coefficient-change-normalization: the existing statement is Normalized coefficient changes and their naturality (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing statement is Derived pro-etale direct image commutes with restriction of scalars (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-ringed-triple-resolution-formulas: the existing statement is Common-resolution formulas for two triple direct-image paths (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs def-pur-ringed-coefficient-counit-presentations: the existing statement is Normalized ringed coefficient counit presentations (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement is Completed-coefficient pushforward restriction and strict reduction towers (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement computes the transpose of arbitrary R_g(v) composed with w through the specified finite pro-etale compositor, including both Hom bijections.

lem-pur-ordinary-derived-composite-transpose vs lem-pur-finite-proper-product-transpose: the item additionally assembles the two counits into Omega and proves product-swap symmetry; the extracted statement is strictly smaller and independent of those final claims.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-derived-direct-image-composition: the existing theorem gives functor composition and coherence, without the stated arrow-level transpose identity.

lem-pur-ordinary-derived-composite-transpose vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing theorem states equality of two exchange/projection naturality composites, not the pair of leg transposes nor the arbitrary-arrow transport identity.

lem-pur-ordinary-derived-composite-transpose vs lem-trf-exceptional-kunneth-counit: the existing theorem is for exceptional constructible finite-Tor adjunctions and the exceptional Kunneth map, not ordinary unbounded pullback/direct-image adjunctions.

lem-pur-ordinary-derived-composite-transpose vs lem-sf-kv-alpha-transpose-coherence: the existing theorem concerns exceptional Kunneth alpha composition and swap, not the ordinary unbounded exchange/projection legs or specified compositor calculus.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-coef-enriched-sequence-projection-formula: the existing statement is Uncurried finite projections of the enriched sequence adjunction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-coef-sequence-sections-limit-comparison: the existing statement is Derived sections and total limit with specified projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-coef-sequence-pushforward-limit-projections: the existing statement is Restricted total-limit comparison with adjunction projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-coef-sequence-global-sections-evaluation: the existing statement is Derived termwise global sections with finite evaluation and transition normalization (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-coef-derived-sections-scalar-coherence: the existing statement is Coherent unit-normalized scalar comparison for unbounded derived global sections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-trf-completion-unit-models: the existing statement is Ordinary quotient adjunction and normalized derived completion models (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-trf-completion-unit-canonical-models: the existing statement is Compatible ordinary and derived presentations of the coefficient adjunction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-proper-open-tower-single-unit-formula: the existing statement is Single derived-unit formula in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-proper-open-tower-successive-unit-formula: the existing statement is Successive derived-unit formula in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-proper-open-tower-derived-unit: the existing statement is Derived-unit resolution calculation in a proper/open tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-ringed-comparison-tensor-adjunction: the existing theorem compares two ringed paths and their monoidality/conjugacy, without the displayed two-leg or unit-insertion transport calculation.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-exact-compactification-unit-refinement: the existing statement is Normalized exact compactification units respect canonical refinements (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-integral-quotient-direct-image-comparison: the existing statement is Unbounded quotient-scalar refinement of integral direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-exact-compactification-unit-composition: the existing statement is Composition of normalized exact compact-support units (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-sfb-ringed-derived-comparison-data: the existing statement is Data of normalized derived monoidal comparisons of ringed topoi (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-ringed-kunneth-factorizations: the existing theorem treats two endomorphism paths over one map q with inputs on the same source X, rather than the separate leg identities or arbitrary composable-arrow and isomorphism-transport formulas.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-ringed-derived-composition-comparison: the existing statement is Composition comparison with normalized representative formulas (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-ringed-derived-identity-comparison: the existing statement is Identity comparison with normalized representative formulas (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-derived-composition-adjunction-normalization: the existing theorem constructs the normalized K-injective composition comparison; it does not state the displayed arbitrary-arrow successive-transpose formula.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sfb-ringed-derived-monoidal-comparisons: the existing theorem normalizes functor comparisons, counits and 2-isomorphisms, but does not state the displayed arbitrary-arrow composite or isomorphism-transport transpose calculation.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing statement is Identity and pasting for ordinary ambient ringed exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing statement is Canonical composition comparison for unbounded ringed-topos direct images (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing statement is Derived adjunctions under compatible changes of ring sheaves (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-weil-pbc-derived-direct-image-composition: the existing statement is Composition isomorphisms of derived direct images (conjugates of those of inverse images) (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-weil-pbc-adjunction-conjugate: the existing statement is Conjugate transformations of adjoint functors (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-ring-sheaf-change-adjunction-existence: the existing statement is Existence of the normalized derived direct-image comparison (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-frobenius-exchange-restriction: the existing statement is Finite-level exchange is the restricted ambient exchange (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-asd-proper-finite-coefficient-extension-core: the existing statement is Unbounded proper coefficient comparison and restricted projection identity (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-coefficient-projection-cocycle: the existing statement is Coefficient projection cocycle for ordinary derived ringed diagrams (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-coefficient-derived-presentation-exists: the existing statement is Existence of a normalized derived coefficient presentation (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-pur-sequence-adjoint-resolution-data: the existing statement is Resolution data for the coefficient sequence projection (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sp-restriction-transition-transpose: the existing statement is Scalar-adjunction transpose of a compact-support mixed-coefficient map (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-cbc-strict-tower-direct-image-coherence: the existing statement is Coherence of canonical strict-tower direct image and its square mates (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-kun-module-abelian-kinjective-direct-image-acyclic: the existing statement is Abelian direct-image acyclicity of a module K-injective complex (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-completed-coefficient-site-data: the existing statement is Exact scalar restrictions, strict-system restriction and derived limit on one site (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-system-pushforward-restriction-transition: the existing statement is Restriction-form transition of simultaneous derived direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sf-compact-support-restriction-of-scalars: the existing statement is Finite-level compact-support direct image commutes with restriction of scalars (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-completed-coefficient-structure-map: the existing statement is Unique completed coefficient structural map from finite projections (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-sequence-adjoint-resolution-shifts: the existing statement is Resolution-normalized identification of the sequence-site derived adjoints (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-derived-composition-cocycle: the existing statement is Cocycle and identity laws for normalized ringed-topos derived composition (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-coefficient-restriction-counit: the existing statement is Derived ringed-topos counit under coefficient restriction (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-proetale-direct-image-global-evaluation: the existing statement is Normalized derived global sections after pro-etale direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-cbc-etale-derived-direct-image-coherence: the existing statement is Ordinary etale derived direct-image composition and its coherence (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-completed-coefficient-direct-image-diagrams: the existing statement is Normalized completed-coefficient direct image on strict diagrams (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-kun-etale-module-abelian-ringed-presentation: the existing statement is Simultaneous ringed presentations of coefficient forgetting and abelian etale direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-diagram-ring-restriction-pushforward: the existing statement is Derived coefficient restriction on ringed diagram topoi (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing statement is Inverse-limit acyclicity of levelwise pushforward of a K-injective tower (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-perfect-quotient-exchange-normalization: the existing statement is Perfect quotient coefficient exchange with augmentation and completion-unit normalization (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-pur-completed-pushforward-models: the existing statement is Normalized models for completed-coefficient direct image (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-asd-proper-finite-coefficient-extension: the existing statement is Canonical unbounded proper direct-image comparison for finite coefficient extension (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-pur-ringed-coefficient-change-presentations: the existing statement is Normalized coefficient changes between counit presentations (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-coefficient-change-normalization: the existing statement is Normalized coefficient changes and their naturality (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing statement is Derived pro-etale direct image commutes with restriction of scalars (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-ringed-triple-resolution-formulas: the existing statement is Common-resolution formulas for two triple direct-image paths (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs def-pur-ringed-coefficient-counit-presentations: the existing statement is Normalized ringed coefficient counit presentations (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement is Completed-coefficient pushforward restriction and strict reduction towers (its stated coefficient/tower, support, scalar or comparison data and conclusion are different); the new statement specifies S_d through a scheme isomorphism and computes the transpose of S_d composed with arbitrary u.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-pur-finite-proper-product-transpose: the item additionally assembles the two counits into Omega and proves product-swap symmetry; the extracted statement is strictly smaller and independent of those final claims.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-derived-direct-image-composition: the existing theorem gives functor composition and coherence, without the stated arrow-level transpose identity.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing theorem states equality of two exchange/projection naturality composites, not the pair of leg transposes nor the arbitrary-arrow transport identity.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-trf-exceptional-kunneth-counit: the existing theorem is for exceptional constructible finite-Tor adjunctions and the exceptional Kunneth map, not ordinary unbounded pullback/direct-image adjunctions.

lem-pur-ordinary-derived-isomorphism-transport-transpose vs lem-sf-kv-alpha-transpose-coherence: the existing theorem concerns exceptional Kunneth alpha composition and swap, not the ordinary unbounded exchange/projection legs or specified compositor calculus.

## Review by Q119

I checked the return against the live item, its recorded Lean declaration, all statements cited in the new item, and the Stacks/current blueprint texts above. The item statement is byte-for-byte unchanged. Each new statement introduces its finite coefficient datum, all schemes/maps, all derived objects and the exact arrows it compares. None relies on 'the setting of' another lemma or a Stacks tag for its meaning. The definition/operation references are in `stmt_deps`; new proofs and proof dependencies are empty. Previously supplied arguments are in this report for the workers, not smuggled into statement-only nodes. Old searches were kept; every new search record is backed by the actual log.

Assembly Step 1 cites the leg lemma, whose conclusion literally contains both displayed transpose formulas with mu and theta; its hypotheses allow the proper maps in the item, since those are separated finite type. The square substitutions are f=a, g=b, f'=t, g'=r, so x has source P_b R_a H and target R_t P_r H. The first projection has target R_t(P_r H tensor P_t J). For w the projection takes R_b J tensor F, explaining its input symmetry, and has target R_b(J tensor P_b F), explaining its output symmetry. No sign was suppressed. The original calculation moved the output symmetry through the counit by naturality and canceled the two symmetries; that exact argument is retained below for the leg task. The statement proves no Omega or swap clause, so it does not replace the entire item.

Assembly Step 2 cites the composite-transpose lemma with f=t, g=b, Q=P_b F tensor J, M=F tensor G and N=E. Its statement gives exactly both the actual c-adjunction transpose and the composite Hom-bijection expression. The arbitrary v and w have precisely the required types. I checked the old calculation: counit naturality for v:Q to R_t E rewrites epsilon_b,R_t E composed with P_b(R_b v) as v composed with epsilon_b,Q. Applying P_t then gives v-hat composed with P_t(w-hat). The finite compositor and constant-coefficient structural-ring bridge must be the canonical ones; the new statement pins those through the same existing ringed normalization theorem. This is not an independent choice of a convenient adjunction. That theorem's statement explicitly supplies adjunction compatibility, so no use of its proof in place of its statement is hidden. This task does not reprove the generic ringed normalization theorem.

Assembly Step 3 cites the full statements of pullback tensor compatibility and pro-etale pullback composition. The former explicitly states naturality, symmetry and compatibility with composition; the latter gives P_c to P_t P_b and to P_r P_a. Thus they justify every identification in the displayed tensor-of-counits calculation. The remaining equality (f tensor identity) composed with (identity tensor g)=f tensor g is the tensor bifunctor's composition law and is written out. These are the original Step 5's arguments, retained in the assembly, not discarded to achieve a length bound.

Assembly Step 4 cites the isomorphism-transport lemma. Its statement explicitly identifies S_d with the canonical transport and computes its transpose; merely knowing functor composition would not suffice. I checked s:C to C', c=c' s and d:P_s E' to E: r' s=t and t' s=r, so d is the signed symmetry after pullback composition. The displayed S_d has source R_c' E' and target R_c E. The original proof uses the exact site equivalence to make eta_s invertible, then composite-counit normalization, counit naturality, and epsilon_s,P_s E' composed with P_s eta_s,E'=identity. All those arguments remain in the transport task below. The output is d composed with P_s(u-hat), with the comparison alpha on its source. No bounded derived-equivalence hypothesis is needed: the exact inverse sheaf functors apply termwise and preserve quasi-isomorphisms.

Assembly Step 5 cites the tensor/composition comparisons and the ordinary derived operations node. I opened those statements: the tensor theorem explicitly supplies signed symmetry and composition compatibility, and the operations node explicitly supplies a bifunctorial Hom bijection on all unbounded inputs. Swapping a,H with b,J in Step 3 and applying Step 4 gives exactly the two signed symmetries in the displayed equality. Naturality moves each degree-zero counit through the symmetry, and symmetry squared is identity. Injectivity of that same Hom bijection, rather than a stalk or cohomology argument, proves the forward-arrow equality. This preserves the original Step 7 in full mathematical detail.

For the extracted statements I tested zero objects, empty schemes, identity maps and odd shifts. The leg identities reduce to identity tensor maps for identities and to zero maps when an input vanishes; odd-shift Koszul signs are present in both symmetries and cancel by naturality/involution. For the composite statement, identity f or g gives the usual naturality formula, and a zero v or w makes both sides zero. For the transport statement, s=identity and d=identity gives the usual transpose; arbitrary nonidentity d remains postcomposition on each side, so it does not accidentally assert a coefficient symmetry. Empty schemes give valid equivalences. At levels n>1, tensor products of bounded objects may be unbounded; every extracted domain and every operation used is ordinary unbounded. Properness, finite Tor, etale origin and constructibility were not silently used. The statements are in derived categories, not merely in each cohomological degree.

The same-tag comparisons are documented above. I specifically avoided adding another generic normalization or monoidal comparison theorem, used the live ones in the task statements, and made the three tasks independently stateable. The only cross-unit proof tools left in the item are the same ordinary pullback/tensor comparison tools and Hom bijection already accepted there; their retained `split_report.tool_uses` explain this use. New task statements reference the general tools but contain no proof dependencies. No path back through this item is introduced. Every argument of the returned proof is assigned below; all new nodes are cited by the assembly. No numbered point of the return remains unaddressed.

## Complete retained argument and task assignment

The following is copied verbatim from the current live seven-step proof. It is the argument to be formalized/split by the independently assignable tasks, not proof content in their JSON records. Original Steps 1 and 4 belong to the composite task, 2 and 3 to the legs task, and 6 to transport; 5 and 7 are realized by the new assembly.

### Original Step 1

Fix the finite coefficient ring and write $P_u=Lu^*$, $R_u=Ru_*$; all tensors below are derived over $A$. The ordinary unbounded operations and adjunctions are those of [def-weil-pbc-proetale-operations]. The constant-ring structure maps compose by [lem-pur-proetale-constant-ring-composition], so composable scheme maps give precisely the composite ringed-topos morphism. Apply [lem-sfb-ringed-derived-monoidal-comparisons] to these ringed topoi: the pullback tensor comparisons are symmetric monoidal and the K-injective direct-image compositor is adjunction-compatible with pullback composition. Its finite-level specialization is the canonical compositor of [lem-weil-derived-direct-image-composition]. Consequently, after the stated comparisons, $\varepsilon_{bt,K}=\varepsilon_{t,K}\circ P_t(\varepsilon_{b,R_tK})$. This fixes the actual counit, rather than merely choosing some adjunction on isomorphic functors. All later formulas insert these same comparisons.

Cited statements: def-weil-pbc-proetale-operations, lem-pur-proetale-constant-ring-composition, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-derived-direct-image-composition.

### Original Step 2

Put $Q=P_bF\otimes J$ and $T=P_rH$. The exchange definition [def-exchange-projection] gives $\varepsilon_{t,T}\circ P_t(x)=P_r(\varepsilon_{a,H})$ after the square pullback comparison. The projection map in that same definition satisfies $\varepsilon_{t,T\otimes P_tJ}\circ P_t(\pi_{t;T,J})=(\varepsilon_{t,T}\otimes1)\mu_t$. Therefore naturality of $\mu_t$ [lem-pur-derived-pullback-tensor-iso] and tensor bifunctoriality give
$$\widehat v=\varepsilon_{t,E}\circ P_t(v)=(\varepsilon_{t,T}\circ P_t(x))\otimes1_{P_tJ}=P_r(\varepsilon_{a,H})\otimes1_{P_tJ}.$$
This is a calculation with the defining transposes, and uses no invertibility of $x$ or $\pi_t$.

Cited statements: def-exchange-projection, lem-pur-derived-pullback-tensor-iso.

### Original Step 3

Transpose $w$ under $P_b\dashv R_b$. Naturality of the counit moves the postcomposed $R_b(\sigma_{J,P_bF})$ outside the transpose. The projection definition [def-exchange-projection] then gives, under $\mu_b$,
$$\widehat w=\sigma_{J,P_bF}\circ(\varepsilon_{b,J}\otimes1_{P_bF})\circ\sigma_{P_bF,P_bG}=1_{P_bF}\otimes\varepsilon_{b,J}.$$
Indeed the last equality is naturality of the signed symmetry followed by $\sigma_{J,P_bF}\circ\sigma_{P_bF,J}=1$. Pullback carries the input symmetry to the displayed one by [lem-pur-derived-pullback-tensor-iso]. Both counits and all morphisms being tensored have degree zero; no assertion that the symmetry itself has trivial Koszul signs is used.

Cited statements: def-exchange-projection, lem-pur-derived-pullback-tensor-iso.

### Original Step 4

Compute the composite transpose, keeping $Q=P_bF\otimes J$. By Step 1 and the composite hom bijection [def-weil-pbc-composite-adjunction], the transpose of $\kappa_{b,t}^{-1}\circ R_b(v)\circ w$ is
$$\varepsilon_{t,E}\circ P_t(\varepsilon_{b,R_tE})\circ P_tP_b(R_bv)\circ P_tP_b(w).$$
Naturality of $\varepsilon_b$ for $v:Q\to R_tE$ rewrites the middle pair as $P_t(v)\circ P_t(\varepsilon_{b,Q})$. Hence the displayed arrow equals
$$\bigl(\varepsilon_{t,E}\circ P_t(v)\bigr)\circ P_t\bigl(\varepsilon_{b,Q}\circ P_b(w)\bigr)=\widehat v\circ P_t(\widehat w).$$
The cancellation of $\kappa$ here is justified by the adjunction compatibility of [lem-sfb-ringed-derived-monoidal-comparisons], not just by associativity of direct images.

Cited statements: def-weil-pbc-composite-adjunction, lem-sfb-ringed-derived-monoidal-comparisons.

### Original Step 5

Insert Steps 2 and 3 into Step 4. Pullback tensor naturality gives $P_t(\widehat w)=1_{P_tP_bF}\otimes P_t(\varepsilon_{b,J})$. Use $P_tP_b=P_c=P_rP_a$ through [lem-weil-pbc-proetale-derived-pullback-composition]; compatibility of these comparisons with tensor is [lem-pur-derived-pullback-tensor-iso]. Thus
$$\widehat\Omega_{a,b}=(P_r\varepsilon_{a,H}\otimes1)\circ(1\otimes P_t\varepsilon_{b,J})=P_r\varepsilon_{a,H}\otimes P_t\varepsilon_{b,J}.$$
The last equality is the composition law for a bifunctor. This proves all three transpose formulas and the asserted composite hom-bijection formula.

Cited statements: lem-weil-pbc-proetale-derived-pullback-composition, lem-pur-derived-pullback-tensor-iso.

### Original Step 6

For the swap write $s=\bar s:C\to C'$, $E'=P_{r'}J\otimes P_{t'}H$, and $d:P_sE'\to E$ for the pullback comparisons followed by $\sigma_{P_tJ,P_rH}$. The isomorphism of sites in [lem-weil-proetale-isomorphism-inverse-image] makes $P_s\dashv R_s$ an equivalence on the ordinary derived categories (apply its exact inverse functors termwise). Its unit $\eta_s$ is invertible. With $c's=c$, the specified transport is
$$S_{a,b}=R_c(d)\circ\kappa_{c',s}^{-1}\circ R_{c'}(\eta_{s,E'}).$$
For any $u:M\to R_{c'}E'$, its transported transpose, using Step 1, is
$$d\circ\varepsilon_{s,P_sE'}\circ P_s(\varepsilon_{c',R_sP_sE'})\circ P_sP_{c'}(R_{c'}\eta_{s,E'}\circ u).$$
Naturality of $\varepsilon_{c'}$ moves $\eta_{s,E'}$ to the left of $\varepsilon_{c',E'}$; the triangle identity $\varepsilon_{s,P_sE'}\circ P_s(\eta_{s,E'})=1$ cancels it. The result is exactly $d\circ P_s(\widehat u)$. Composition and transport use [lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-derived-direct-image-composition], so this calculation concerns the stipulated $S_{a,b}$.

Cited statements: lem-weil-proetale-isomorphism-inverse-image, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-derived-direct-image-composition.

### Original Step 7

Apply Step 5 with $(a,H)$ and $(b,J)$ interchanged, and then Step 6 to $u=\Omega_{b,a}$. Precomposing by $\sigma_{F,G}$ precomposes the transpose by $P_c(\sigma_{F,G})$. The pullback/tensor and composition comparisons [lem-pur-derived-pullback-tensor-iso, lem-weil-pbc-proetale-derived-pullback-composition] identify the result with
$$\sigma_{P_tJ,P_rH}\circ(P_t\varepsilon_{b,J}\otimes P_r\varepsilon_{a,H})\circ\sigma_{P_rP_aF,P_tP_bG}=P_r\varepsilon_{a,H}\otimes P_t\varepsilon_{b,J}.$$
This is signed symmetry naturality and its involution identity. It equals $\widehat\Omega_{a,b}$ by Step 5. Injectivity of the ordinary adjunction hom bijection [def-weil-pbc-proetale-operations] proves the claimed equality of forward maps. No boundedness, finite Tor, etale-origin or constructibility condition entered any step.

Cited statements: lem-pur-derived-pullback-tensor-iso, lem-weil-pbc-proetale-derived-pullback-composition, def-weil-pbc-proetale-operations.
