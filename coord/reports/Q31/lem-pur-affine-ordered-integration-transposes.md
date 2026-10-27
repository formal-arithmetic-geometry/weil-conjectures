## Worker report

Stage 2 statement of `lem-pur-affine-ordered-integration-transposes`, preserving Q109's accepted stage-1 split. The stage-handoff paragraph of `coord/brief-stage2.md` explicitly authorizes this statement work; the inherited stage-1 stale-dispatch ending is not a stage-2 failure. No source statement, proof step, dependency list, or reviewed split is changed.

The module is `Sheaf.Paper.AffineOrderedIntegrationTransposes`, namespace `AlgebraicGeometry.ProEtale.AffineOrderedIntegration`. All theorem proofs are `sorry`. Definitions contain actual composites, recursive maps, or selections from uniqueness statements fixing the hom by heterogeneous equality to an explicitly constructed map. None selects an unspecified orientation, natural isomorphism, or arbitrary morphism.

### Hypotheses and objects

- The finite-field, prime, finite coefficient extension, uniformizer quotient, and positive level are the existing `P : WeilConjectures.PurityFiniteSetting`. `AffineLinePurity.Ring P` is the existing lifted finite coefficient ring at zero-based index `P.level - 1`, canonically the quotient at positive level `P.level`. `exponent P = ell^(P.level+1)` is an annihilator, not a restriction on ramification or level; `annihilates P` is the published proof interface.
- The structure morphism is `aY : Y ⟶ Spec (.of P.field.k)`. `[LocallyOfFiniteType aY] [QuasiCompact aY]` is finite type and `[IsSeparated aY]` is separatedness. Noetherianity is obtained from `tower_noetherian`; it is not an additional assumption in the main statement.
- `iteratedAffineLine Y d`, `iteratedAffineLineProj Y d`, and `lastProjection Y d` are the already recorded coordinate model, with literal identity at zero and the last coordinate added at each successor. They use Mathlib affine space, not a second scheme construction.
- The pro-etale category is the published `D P Y` / `C A Y`, on `Scheme.ProEt.topology Y` with `ModuleCat.{u+1} A`; the small-site object and morphism universes remain distinct. `tensor` and `inverseImage` are the dependency's fixed-scalar coordinates for the recorded derived operations.
- `K : Plus A Y`, `Ke : Etale.DerivedCategoryModule A Y`, `hKe : etaleFiniteTor A Y Ke`, and `eK : comparison.obj Ke ≅ K.obj` present precisely a bounded constructible finite-Tor input with an etale origin. The origin theorem supplies such a witness for every input of the node; this does not restrict the input to a smaller class. All witnesses are universally quantified. No flatness of A over a Kummer coefficient ring is assumed.

### Clauses and the Lean that renders them

- `orderedAdjunction` specializes the recorded `Etale.affineTraceAdjunction` to the normalized `projectiveLineTraceTransport` and `projectiveLineTraceDatum`. Its left and right functors are the explicit ordered tower, including the identity adjunction at zero.
- `ordinaryCompactComparison` is the canonical proper/open identification of the ordered left functor with ordinary `Rp_d!` on bounded-below objects. Its arrows are `affineTracePlusCompatibility`, `affineTraceCompactSupportComparison`, and `rightDerivedLowerShriekPlusCompatibility`; no new adjoint comparison is chosen.
- `CompositionSiteEquation` and `coordinate_coherence` state the ordinary/pro-etale compositor square. `coherenceCompositionData.proMap` contains the published `originCompositionAmbient`, which is the underlying actual alpha of `thm-sf-comp-composition`. Quantification over the compactifications covers the specified product-of-projective-lines presentation and compatible triangle; the square uses the canonical change-of-compactification maps.
- `OrdinaryProjectionCompositionEquation` is the displayed PF composition equation in coefficient-first tensor coordinates on the ordinary site. `ProProjectionCompositionEquation` and `pro_coordinate_projection_composition` give the pro-etale equation with `originCompositionAmbient` itself, retaining the two origin witnesses necessary to evaluate its components and the canonical `inverseImageComp` on the source. The factors appear in Lean's left-to-right `≫` convention. Tensor symmetries implement the node's right-coefficient display.
- `ProTensorActionEquation` and `OrdinaryTensorActionEquation`, asserted in `coordinate_coherence`, are the compactification tensor-action identity with the literal associator and tensor-pullback comparison, on both sites. The temporary finite-ring Noetherian instance is derived from finiteness, not hypothesized.
- `etaleCoefficient`, `coefficientComparison`, and `ordinaryTraceRaw` render A(d)[2d], the canonical Tate source identification, and the ordered counit at A after the normalized tower compositor. `ordinaryTrace` only transports this exact arrow between identical coordinate models: its uniqueness condition is `HEq` to `ordinaryTraceRaw`.
- `ordinarySourceDescent` and `ordinarySourceIso` construct the coefficient source normalization for arbitrary K by the actual identity pullback, tensor unit, normalized Tate pullback, inverse-image composition and tensor associator. Their uniqueness condition fixes the zero component and every successor hom by the explicit corresponding raw composite.
- `ordinaryCounit` is the ordered adjunction counit after `ordinaryCompactComparison`. `ordinary_counit_formula` states exactly epsilon = (1_K tensor t) Pi, precomposed with the canonical forward projection. That projection is invertible on the stated inputs by the imported ordinary projection theorem, so this is equivalent to the node's inverse-projection formula and avoids choosing an extra inverse.
- `trivial_frame_integration` identifies the published `vectorBundleIntegration` with its local formula for the particular normalized ordered datum. `coordinateModule` is just the existing free module sheaf. `framedTraceFixed` is the published `vectorIntegrationLocalTrace`, whose definition ends in that ordered counit; its prefix is the canonical exchange and coefficient descent. Thus the trace used here is precisely vector integration in a trivial frame, not a new trace satisfying an unrecorded axiom.
- `coordinate_site_comparison` specializes the published `FiniteTypeSiteCompatibility` at `P.level - 1` and the free rank-d sheaf. It includes the projective trace, restricted open counit, vector integration, inverse projection, and exceptional transpose comparison equations for every annihilating exponent and finite-Tor coefficient input.
- `realizeTrace` constructs the pro-etale integration from that ordered ordinary trace using the actual compact-support site comparison. `augmentation` is the literal inverse projection, tensor with that integration, and right unitor. `standingTranspose` applies the specified restricted exceptional Hom bijection. `integrationTransposeRaw` composes the actual source-coordinate identification with that transpose. `integrationTranspose` transports this same computed hom to `ComparisonHom`, with the map uniquely fixed by `HEq`; it is not defined in terms of Gamma.
- `ordered_integration_transposes` first asserts `integrationTranspose = affineSpacePurityComparison` for every d, then its invertibility. `exceptionalComposite` is the dependency's inverse conjugate of the actual alpha, and its asserted invertibility is the isomorphism convention for c_m in the node. The successor conjunct is exactly I followed by twisted pullback of P, the line map at the actual exceptional target, and c inverse. `exceptionalLine` uses `stageEtale`, `stageComparison`, and `stage_applicability`, with target `exceptional P Y d`, not an independently chosen isomorphic object.
- `source_applicability` retains boundedness and finite-Tor constructibility of the explicit tensor source. The dependency `stage_applicability` retains those properties for the actual exceptional target; hence the next line input is in D^b_ctf. The IsIso conjunct identifies that target with the ordered source via P itself.
- The naturality conjunct uses `sourceLine` at G_dK and `exceptionalLine` at Rp_d!K and states the node's exact square with `rightDerivedUpperShriek.map P`. The last `HEq` conjunct gives P_0 = identity in the normalized rank-zero coordinates. Shift factors are the recorded shifted Tate line [2] repeated d times, hence every shift is even.

### Edge cases

The coordinate model has literal X_0=Y; both the main transpose and Gamma use identity at d=0. The source right unitor and inverse-image identity are included explicitly, so an unnoticed scalar at rank zero is not permitted. All quantifiers allow K=0 and the empty scheme Y; no nonemptiness assumption or chosen geometric point occurs. The annihilator ell^(level+1) works at every positive level, including level one and levels not divisible by the ramification index. No independent small index universe, ambient pro-etale projection isomorphism, or extra flatness assumption occurs.

### Dependency declarations read and reused

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting` and its published finite-coefficient helpers.
- `def-weil-scheme-morphism-properties`: convention/pointer node; use Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` as specified there.
- `def-sbc-affine-space`: Mathlib `AlgebraicGeometry.AffineSpace` and its canonical projection.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique` and its published finite-coefficient helpers.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor` and its published finite-coefficient helpers.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` and its published finite-coefficient helpers.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System` and its published finite-coefficient helpers.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration`, `AlgebraicGeometry.Etale.vectorBundleIntegration` and its published finite-coefficient helpers.
- `lem-pur-vector-integration-site-comparison`: `Sheaf.Paper.VectorIntegrationSiteComparison`, `AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeSiteComparison` and its published finite-coefficient helpers.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its published finite-coefficient helpers.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale` and its published finite-coefficient helpers.
- `lem-amb-affine-space-top-trace`: `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`, `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace` and its published finite-coefficient helpers.
- `thm-sf-comp-composition`: `Sheaf.Paper.CanonicalOriginCompactSupportComposition`, `AlgebraicGeometry.ProEtale.originComposition` and its published finite-coefficient helpers.
- `def-pur-affine-space-comparison`: `Sheaf.Paper.AffineSpacePurityComparison`, `AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComparison` and its published finite-coefficient helpers.
- `def-amb-p1-trace`: `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`, `AlgebraicGeometry.Etale.projectiveLineTrace` and its published finite-coefficient helpers.

The main recorded declaration in some multi-stage dependency records is the last coefficient-stage interface; its module publicly retains the finite-level definitions used here. These records are usable, and no dependency re-recording is required. Proof-dependency imports retain the existing ordinary projection, composition-mate, composite-counit, site-transport, constructible-origin and finite-Tor preservation statements. Mathlib supplies `Adjunction.comp`, `conjugateEquiv`, and right-adjoint uniqueness.

### Searches

Actual launcher search receipts are retained in sandbox `searches.jsonl`. LeanFinder query “ordered affine adjunction counit integration exceptional transpose compact support composition” returned general categorical/condensed counits, including `CategoryTheory.Adjunction.comp_counit`, but no normalized geometric statement. Loogle `CategoryTheory.Adjunction.comp` returned that general composition construction and its unit/counit equations, not this node. Earlier unqualified `Adjunction.comp` and `Adjunction.homEquiv` queries returned unknown identifiers; the qualified query corrects that unsuccessful search. Launcher grep `integration.*transpose|affine.*trace|Adjunction.comp` in Mathlib CategoryTheory returned the adjunction machinery only.

Ripgrep in both `lean/WeilConjectures` and `lean/Sheaf` for `ordered_integration_transposes`, integration transposes, ordered affine traces, and the node id found the recorded affine-space comparison, generic transpose-composition/base-change lemmas, and the ordered integration construction. None states the present conjunction with the actual alpha, its projection/counit/site equations, and P=Gamma. The upstream ordinary-etale affine-space file explicitly says it does not construct the comparison maps, so its existence of an unspecified isomorphism is not a match. The existing vector integration, finite-Tate coefficient, affine tower, ordinary adjunction and affine-space Gamma are all reused.

No statement correction, disputed mathematical statement, new independent notion, or dependency interface repair is proposed.

## Second reading by Q31

A second pass opened the current accepted node and this module and checked the hypotheses and every conclusion against the mapping above. The kept draft initially stated only P=Gamma, invertibility, recursion, naturality and rank zero. It omitted explicit statements for the compositor square, PF composition, tensor action, ordered coefficient-counit formula, trivial-frame normalization and site transport. Those omissions were repaired by adding the named clause statements listed above. The main P is constructed independently from integration and inverse projection before the equality theorem. The right-adjoint target in the recursion remains the actual exceptional object, and origin/finite-Tor proofs are conclusions or existing theorem applications rather than purity hypotheses. No independent reviewer was spawned: this dispatched brief forbids other agents, and the maintainer performs the independent delivery review.

## Validation

The prescribed scompile.py compiled the complete delivered file cleanly on the server,
both in the sandbox namespace (25.0 seconds) and under its library module name
(27.9 seconds). Development diagnostics were removed. Two public category instances
reuse the existing derived-category instances verbatim, and the generic
ProProjectionCompositionLaw packages the quantified witnessed domain before coordinate
specialization; these avoid repeated elaboration through the finite quotient ring
without changing any mathematical map or hypothesis. Every delivered declaration is
listed in lean.declarations. Only the item's lean field changes in the copied node.
