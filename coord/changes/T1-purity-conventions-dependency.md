# def-pur-conventions

## Reason

Repair of all six cycle findings on returned head 791a2e9a6f1. The conventions node incorrectly makes the Frobenius scalar theorem a prerequisite for constructing its data. The live PurityFiniteSetting module is completely constructed and proved without that theorem. Its public imports and attached declarations contain no scalar computation or dependency on TwistFrobeniusScalar. Keep the canonical Weil structures as specified coefficient data, and leave the Frobenius computation in its existing separate theorem. This is a DAG/prose correction only: no Lean signature, definition body, theorem proof, import, or unit realization changes. The unit sk-def-purity-conv has no realized statement or steps to bypass.

## Old

Fix the global finite-field datum $(p,a,q,k_0,k)$ of [def-weil-finite-field-fiber], with $p$ prime, $a\geq1$, $q=p^a$, $k_0=\mathbf F_q$ and $k$ its fixed algebraic closure. Fix a prime $\ell\ne p$, a finite extension $E/\mathbf Q_\ell$ contained in the fixed algebraic closure $\overline{\mathbf Q}_\ell$, its valuation ring $\mathcal O_E$, a uniformizer $\varpi_E$, and $n\geq1$, and put
$$
 A=A_{E,n}=\mathcal O_E/\varpi_E^n
$$
as in [def-weil-l-adic-coefficient-extension].

For a $k$-scheme $Y$, use its small pro-etale site [def-weil-pbc-proetale-site]. The finite coefficient category $D^b_c(Y,A)$ is the bounded constructible category of [def-weil-finite-torsion-constructibility]. At integral coefficients use $D^b_c(Y,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed], with its derived completeness and a single cohomological interval for all finite reductions; its ambient coefficient ring sheaf is $\widehat{\mathcal O}_{E,Y}=\varprojlim_j(A_{E,j})_Y$ [def-weil-completed-integral-coefficients]. The rational category $D^b_c(Y,E)$ is the scalar localization of [def-weil-rationalization-karoubi], and $D^b_c(Y,\overline{\mathbf Q}_\ell)$ is the common-stage category of [def-weil-algebraically-closed-coefficients]. Use the finite-Tor subcategories $D^b_{ctf}(Y,\Lambda)$ for $\Lambda\in\{A,\mathcal O_E,E,\overline{\mathbf Q}_\ell\}$ exactly as in [def-weil-finite-tor-amplitude]: at the integral stage the Tor interval is uniform in all reductions, and at the two field stages $D^b_{ctf}=D^b_c$.

Use the derived pullback, tensor product and internal Hom of [def-weil-derived-pullback-tensor-hom], on the domains specified there, and the cohomology sheaves $\mathcal H^r$ of [def-weil-derived-cohomology-sheaves]. For a separated finite-type $k$-morphism $f:X\to Y$ between finite-type $k$-schemes [def-weil-proper-morphism, def-weil-finite-type-morphism], use the finite-level compact-support direct image $Rf_!$ of [def-compact-support-direct-image-detailed], its higher-coefficient constructions of [def-weil-integral-rational-qbar-compact-support], and the constructible exceptional inverse image $Rf^!$ of [def-weil-exceptional-inverse-image], with the adjunction $Rf_!\dashv Rf^!$ on the bounded constructible categories specified in that definition. Use the exchange and projection maps of [def-exchange-projection], on its stated domains and with its specified comparison data. These conventions name the functors and maps; preservation and invertibility assertions are the separate statements about them.

Let $\Lambda_Y$ denote the coefficient unit: $(A_{E,n})_Y$ in degree zero at finite level, $\widehat{\mathcal O}_{E,Y}$ at the integral level, and its rationalized or common-stage image at the field levels. Use the coefficient twists of [def-coefficient-twists-detailed] for every $m\in\mathbf Z$:
$$
 K(m)=K\otimes^L_{\Lambda_Y}\Lambda(m)_Y.
$$
Here $\otimes^L_{\Lambda_Y}$ is the derived tensor product of sheaves of $\Lambda_Y$-modules exactly as specified in [def-coefficient-twists-detailed] (over the completed sheaf $\widehat{\mathcal O}_{E,Y}$ at the integral level); for $\Lambda\in\{E,\overline{\mathbf Q}_\ell\}$ it is formed on an integral representative, as there. Smooth of relative dimension $d\geq0$ has the meaning of [def-sbc-smooth-morphisms]. Statements and constructions in the finite-coefficient part of the purity chapter are made for $\Lambda=A$; the $\mathcal O_E,E,\overline{\mathbf Q}_\ell$ versions are the derived-complete, rationalized and common-stage coefficient transports specified in the chapter's transport section.

Use the canonical Weil structures on the twists of [def-weil-frobenius-coefficient-twists]. The geometric-Frobenius normalization on the coefficient line over $\operatorname{Spec}k$ is the scalar action of [lem-pur-twist-frobenius-scalar]: $q^{-1}$ on $\Lambda(1)$, $q^{-m}$ on $\Lambda(m)$, and $q^m$ on $\Lambda(-m)$ for $m\geq0$, compatibly with finite reduction and scalar extension.

For a separated finite-type $k$-scheme $Y$, with structure morphism $a_Y:Y\to\operatorname{Spec}k$, define
$$
 \omega_{Y,\Lambda}:=Ra_Y^!\Lambda_{\operatorname{Spec}k}.
$$
Here $Ra_Y^!$ is the constructible exceptional inverse image just specified; no exceptional-adjoint admissibility datum is added.

stmt_deps additionally contains `lem-pur-twist-frobenius-scalar`.

## New

Fix the global finite-field datum $(p,a,q,k_0,k)$ of [def-weil-finite-field-fiber], with $p$ prime, $a\geq1$, $q=p^a$, $k_0=\mathbf F_q$ and $k$ its fixed algebraic closure. Fix a prime $\ell\ne p$, a finite extension $E/\mathbf Q_\ell$ contained in the fixed algebraic closure $\overline{\mathbf Q}_\ell$, its valuation ring $\mathcal O_E$, a uniformizer $\varpi_E$, and $n\geq1$, and put
$$
 A=A_{E,n}=\mathcal O_E/\varpi_E^n
$$
as in [def-weil-l-adic-coefficient-extension].

For a $k$-scheme $Y$, use its small pro-etale site [def-weil-pbc-proetale-site]. The finite coefficient category $D^b_c(Y,A)$ is the bounded constructible category of [def-weil-finite-torsion-constructibility]. At integral coefficients use $D^b_c(Y,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed], with its derived completeness and a single cohomological interval for all finite reductions; its ambient coefficient ring sheaf is $\widehat{\mathcal O}_{E,Y}=\varprojlim_j(A_{E,j})_Y$ [def-weil-completed-integral-coefficients]. The rational category $D^b_c(Y,E)$ is the scalar localization of [def-weil-rationalization-karoubi], and $D^b_c(Y,\overline{\mathbf Q}_\ell)$ is the common-stage category of [def-weil-algebraically-closed-coefficients]. Use the finite-Tor subcategories $D^b_{ctf}(Y,\Lambda)$ for $\Lambda\in\{A,\mathcal O_E,E,\overline{\mathbf Q}_\ell\}$ exactly as in [def-weil-finite-tor-amplitude]: at the integral stage the Tor interval is uniform in all reductions, and at the two field stages $D^b_{ctf}=D^b_c$.

Use the derived pullback, tensor product and internal Hom of [def-weil-derived-pullback-tensor-hom], on the domains specified there, and the cohomology sheaves $\mathcal H^r$ of [def-weil-derived-cohomology-sheaves]. For a separated finite-type $k$-morphism $f:X\to Y$ between finite-type $k$-schemes [def-weil-proper-morphism, def-weil-finite-type-morphism], use the finite-level compact-support direct image $Rf_!$ of [def-compact-support-direct-image-detailed], its higher-coefficient constructions of [def-weil-integral-rational-qbar-compact-support], and the constructible exceptional inverse image $Rf^!$ of [def-weil-exceptional-inverse-image], with the adjunction $Rf_!\dashv Rf^!$ on the bounded constructible categories specified in that definition. Use the exchange and projection maps of [def-exchange-projection], on its stated domains and with its specified comparison data. These conventions name the functors and maps; preservation and invertibility assertions are the separate statements about them.

Let $\Lambda_Y$ denote the coefficient unit: $(A_{E,n})_Y$ in degree zero at finite level, $\widehat{\mathcal O}_{E,Y}$ at the integral level, and its rationalized or common-stage image at the field levels. Use the coefficient twists of [def-coefficient-twists-detailed] for every $m\in\mathbf Z$:
$$
 K(m)=K\otimes^L_{\Lambda_Y}\Lambda(m)_Y.
$$
Here $\otimes^L_{\Lambda_Y}$ is the derived tensor product of sheaves of $\Lambda_Y$-modules exactly as specified in [def-coefficient-twists-detailed] (over the completed sheaf $\widehat{\mathcal O}_{E,Y}$ at the integral level); for $\Lambda\in\{E,\overline{\mathbf Q}_\ell\}$ it is formed on an integral representative, as there. Smooth of relative dimension $d\geq0$ has the meaning of [def-sbc-smooth-morphisms]. Statements and constructions in the finite-coefficient part of the purity chapter are made for $\Lambda=A$; the $\mathcal O_E,E,\overline{\mathbf Q}_\ell$ versions are the derived-complete, rationalized and common-stage coefficient transports specified in the chapter's transport section.

Use the canonical Weil structures on the twists of [def-weil-frobenius-coefficient-twists]. These conventions specify the coefficient objects and their Weil structures; computing the induced Frobenius scalars is a separate theorem, not data needed to construct the finite coefficient setting.

For a separated finite-type $k$-scheme $Y$, with structure morphism $a_Y:Y\to\operatorname{Spec}k$, define
$$
 \omega_{Y,\Lambda}:=Ra_Y^!\Lambda_{\operatorname{Spec}k}.
$$
Here $Ra_Y^!$ is the constructible exceptional inverse image just specified; no exceptional-adjoint admissibility datum is added.

stmt_deps removes only `lem-pur-twist-frobenius-scalar`. The theorem node and its module remain untouched and needed by actual scalar computations.

## Users

This changes no Lean interface. All 501 direct node consumers below retain their coefficient setting, objects, twists and Weil structures verbatim. Their assertions therefore remain unchanged. Each is also recorded with holds=true in statement_change.citers. The existing scalar theorem continues to supply its computation wherever required. PurityFiniteSetting is unclaimed in current coord/claims. No consumer adaptation is necessary.

| node | module | group holding module | effect |
| --- | --- | --- | --- |
| cor-pur-adic-and-rational-smooth-dualizing-complexes | Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-affine-space-purity | WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-affine-space-zero-section-purity | Sheaf.Paper.AffineSpaceZeroSectionPurity | F4 | Same definitions and theorem statements; no edit. |
| cor-pur-dualizing-object-purity | Sheaf.Paper.DualizingObjectPurity | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-finite-stage-smooth-dualizing-complex | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-general-admissibility-datum | Sheaf.Paper.PurityAffineChartBounds | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-smooth-admissibility | Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | Same definitions and theorem statements; no edit. |
| cor-pur-vector-bundle-purity | Sheaf.Paper.VectorBundlePurity | P4 | Same definitions and theorem statements; no edit. |
| def-pur-adic-finite-source-normalization | Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-adic-normalized-purity-systems | Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-adic-projection-trace-data | Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-adic-root-comparisons | Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-adic-scalar-trace-data | Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-adic-trace-source-coordinates | Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-coefficient-counit-coordinate-maps | Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-diagonal-tate-coordinates | Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-line-datum | Sheaf.Paper.PurityAffineLineDatum | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-line-purity-comparison | Sheaf.Paper.AffineLinePurityComparison | D5 | Same definitions and theorem statements; no edit. |
| def-pur-affine-line-purity-coordinate-maps | Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-line-purity-source | Sheaf.Paper.AffineLinePuritySource | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-space-comparison | Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-affine-space-coordinate-boundaries | Sheaf.Paper.AffineSpaceCoordinateBoundaries | V9 | Same definitions and theorem statements; no edit. |
| def-pur-affine-space-thom-map | Sheaf.Paper.AffineSpaceThomMap | B8 | Same definitions and theorem statements; no edit. |
| def-pur-canonical-rational-purity-realization | Sheaf.Paper.RationalSmoothPurityCanonical | M2 | Same definitions and theorem statements; no edit. |
| def-pur-cartier-agreement-maps | Sheaf.Paper.CartierClassAgreement | B7 | Same definitions and theorem statements; no edit. |
| def-pur-chart-affine-comparison-data | Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-chart-coefficient-adjoint-data | Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same definitions and theorem statements; no edit. |
| def-pur-chart-diagonal-assembly-data | Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-chart-source-comparison | Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-chart-unit-affine-comparison | Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same definitions and theorem statements; no edit. |
| def-pur-chern-classes | Sheaf.Paper.PurityChernClasses | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-canonical-finite-evaluation | Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-canonical-restriction-evaluation | Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-coefficient-operations | Sheaf.Paper.FiniteClopenDerivedDecomposition | J5 | Same definitions and theorem statements; no edit. |
| def-pur-clopen-completed-tower-restriction | Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-exceptional-all-coefficients | Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-ordinary-restriction-realization | Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-restriction-evaluation-data | Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-strict-system-comparison | Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-system-finite-realization | Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-clopen-system-realization-data | Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-co-smoothness | Sheaf.Paper.CohomologicalSmoothnessFiniteComparison | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-product-proper-support-laws | Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-product-realization-core-laws | Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-product-realization-laws | Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-product-twist-laws | Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-support-completed-projection-data | Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-support-completed-scalar-arrow | Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-support-transport | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-compact-support-transpose-constructions | Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Same definitions and theorem statements; no edit. |
| def-pur-composition-comparisons | Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-germ-concentration-data | Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-line-adjunction-maps | Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-product-presentations | Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-arrows | Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-cartier-realization | Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-cartier-sign | Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-ordinary-arrows | Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-projection | Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-projective-arrows | Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-section-site-arrows | Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-coordinate-zero-base-change | Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-diagonal-affine-trace-coordinates | Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-diagonal-chart-transports | Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same definitions and theorem statements; no edit. |
| def-pur-diagonal-dnc-chart-data | Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same definitions and theorem statements; no edit. |
| def-pur-diagonal-dualizing-data | Sheaf.Paper.PurityDiagonalDualizingData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-dnc-section-family | Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-affine-orientation-comparison | Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-first-root-chart | Sheaf.Paper.FiniteFirstRootChart | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-free-projection-exchange-data | Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-orientation-scalar-presentation | Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-positive-root-charts | Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-reduction-root-charts | Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-root-tensor-presentation | Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-section-comparison | Sheaf.Paper.PurityDncFiniteRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-signed-reduction-comparisons | Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-signed-twist-products | Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-site-coordinates | Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-site-tensor-projection | Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-tensor-fixed-comparisons | Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-tensor-reduction-data | Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-finite-trace-presentation-data | Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-flasque-support | Sheaf.AlgebraicGeometry.ProEtalePairFlasque | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-frame-class | Sheaf.Paper.PurityFrameClass | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-frame-kummer-class | Sheaf.Paper.PurityFrameKummer | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-frame-principal-boundary | Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-abelian-realization | Sheaf.Paper.FramedAbelianRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-etale-hom | Sheaf.Paper.FramedEtaleHom | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-forget-support | Sheaf.Paper.FramedForgetSupport | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-pro-predicate | Sheaf.Paper.FramedProPredicate | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-pro-realization | Sheaf.Paper.FramedProRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-realization-additive | Sheaf.Paper.FramedRealizationAdditive | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-realization-enlarge | Sheaf.Paper.FramedRealizationEnlarge | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-realization-iso | Sheaf.Paper.FramedRealizationIso | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-realization-property | Sheaf.Paper.FramedRealizationProperty | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-realization-pullback | Sheaf.Paper.FramedRealizationPullback | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-scalar-maps | Sheaf.Paper.FramedScalarMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-scalar-realization | Sheaf.Paper.FramedScalarRealization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-framed-transport | Sheaf.Paper.FramedTransport | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-general-chart-comparisons | Sheaf.Paper.GeneralChartComparisons | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-integral-compact-support-coefficient-data | Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-kummer-comparison-data | Sheaf.Paper.PurityFiniteKummerDefinitions | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-normal-bundle | Sheaf.Paper.PurityNormalProjection | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-ordinary-finite-flag-products | Sheaf.Paper.ChernFlagFormula | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-orientation-refinement-comparisons | Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same definitions and theorem statements; no edit. |
| def-pur-proetale-affine-line-counit | Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-proetale-frame-integration | Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-proetale-ordered-integration | Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-proetale-projection-integration | Sheaf.Paper.ProEtaleProjectionIntegration | T2 | Same definitions and theorem statements; no edit. |
| def-pur-proetale-projective-coefficient | Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-proetale-vector-integration | Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-proetale-vector-integration-arrows | Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-rank-one-local-data | Sheaf.Paper.PurityRankOneLocalData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-regular-immersion-cancellation | Sheaf.Paper.RegularImmersionCancellation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-regular-immersion-class-data | Sheaf.Paper.RegularImmersionClassData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-regular-immersion-exterior-class | Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-regular-immersion-signed-evaluation | Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-regular-section | Sheaf.Paper.PurityRegularSection | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-scheme-geometric-frobenius | Sheaf.SixFunctors.SchemeGeometricFrobenius | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-section-invariant | Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-section-pullback-site-comparisons | Sheaf.Paper.PurityDncInvariance | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-section-restriction-data | Sheaf.Paper.PuritySectionEtaleRestriction | Y2 | Same definitions and theorem statements; no edit. |
| def-pur-section-tate-pullback | Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same definitions and theorem statements; no edit. |
| def-pur-semilinear-exchange-descent-data | Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-semilinear-exchange-reindexing-data | Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-shifted-tate-unit-scalar-data | Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-smooth-pullback-exchange | Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-smooth-purity-map | Sheaf.Paper.SmoothPurityMap | B4 | Same definitions and theorem statements; no edit. |
| def-pur-smooth-trace | Sheaf.Paper.SmoothTrace | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-class-geometry | Sheaf.Paper.SupportedClassGeometry | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-class-operations | Sheaf.Paper.SupportedCupFunctoriality | Q8 | Same definitions and theorem statements; no edit. |
| def-pur-supported-cup | Sheaf.Paper.SupportedCup | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-exterior-class-arrows | Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-exterior-shift | Sheaf.Paper.SupportedExteriorShift | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-hom-pair | Sheaf.Paper.SupportedHomPullback | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-projection-splitting | Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-projective-chern | Sheaf.Paper.SupportedProjectiveChern | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-supported-projective-site-arrows | Sheaf.Paper.ProEtaleProjectiveLineTrace | E5 | Same definitions and theorem statements; no edit. |
| def-pur-tate-datum | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-td-datum | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-adic-agreement | Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-coefficient-coherence | Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-composite-shifts | Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-pbc-coordinates | Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-pbc-pullback-coordinates | Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-pbc-twist-coordinates | Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-shift-coherence | Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-shift-normalization | Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-square-coordinates | Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-square-maps | Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-twisted-pullback-square-shift-equations | Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-unit-trace-reduction-data | Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-bundle-thom-class | Sheaf.Paper.VectorBundleThomClass | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-bundle-thom-comparisons | Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-bundle-zero-section | Sheaf.Paper.PurityVectorBundleZeroSection | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-purity-finite-reduction | Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-purity-normalization | Sheaf.Paper.VectorPurityNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| def-pur-vector-tensor-site-equations | Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Same definitions and theorem statements; no edit. |
| def-sf-integral-support-refinement-comparison | Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Same definitions and theorem statements; no edit. |
| det-sp-field-extension-towers | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| det-sp-finite-general-ring | Sheaf.SecSmoothPurity.FiniteGeneralRing | X2 | Same definitions and theorem statements; no edit. |
| det-sp-orientation-charts | Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same definitions and theorem statements; no edit. |
| det-sp-orientation-vector-bundle | Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same definitions and theorem statements; no edit. |
| det-sp-trace-basic | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| det-sp-unique-adjoint-coefficients | Sheaf.SmoothPurity.UniqueAdjointCoefficients | unclaimed | Same definitions and theorem statements; no edit. |
| lem-a1-qbar-curve-duality | Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-coef-dualizing-open-adjoint | Sheaf.Paper.CoefficientDualizingOpenAdjoint | M3 | Same definitions and theorem statements; no edit. |
| lem-fd-affine-space-thom-coefficient-transport | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pod-smooth-oriented-exchange-comparisons | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-a1-components | Sheaf.AlgebraicGeometry.PurityAffineLineComponents | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-a1-direct-image | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-normalized-purity-lift | Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-operation-domains-source-comparison | Sheaf.Paper.AdicOperationDomainsSourceComparison | W2 | Same definitions and theorem statements; no edit. |
| lem-pur-adic-projection-shift-coherence | Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-purity-scalar-naturality | Sheaf.Paper.AdicPurityScalarNaturality | R2 | Same definitions and theorem statements; no edit. |
| lem-pur-adic-scalar-extension-tor-bound | Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-scalar-trace-coherence | Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-source-finiteness-reductions | Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-adic-trace-transpose-coefficient-calculus | Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | W3 | Same definitions and theorem statements; no edit. |
| lem-pur-adic-unit-trace-transpose-reductions | Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-chart-exceptional-identification | Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-coefficient-counit-normalization | Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Same definitions and theorem statements; no edit. |
| lem-pur-affine-coordinate-support-stalk-continuity | Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-diagonal-integration-orientation | Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-line-boundary-realization | Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-line-composite-transpose | Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-line-ordinary-invariance | Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-line-orientation-injectivity | Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-line-support-stalk | Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-ordered-integration-transposes | Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Same definitions and theorem statements; no edit. |
| lem-pur-affine-space-last-factor-product | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-space-product-domain | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-space-trace-factorization | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-affine-target-diagonal-dnc | Sheaf.Paper.AffineTargetDiagonalDnc | F1 | Same definitions and theorem statements; no edit. |
| lem-pur-affine-tower-integration-site-transport | Sheaf.Paper.AffineTowerIntegrationSiteTransport | J1 | Same definitions and theorem statements; no edit. |
| lem-pur-affine-translation-trace | Sheaf.Paper.AffineTranslationTrace | Z8 | Same definitions and theorem statements; no edit. |
| lem-pur-all-stage-ctf-pullback-unit | Sheaf.Paper.AllStageCtfPullbackUnit | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-base-changed-line-trace-evaluation | Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-bounded-site-adjunction-transpose | Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-bounded-site-compositor-conjugates | Sheaf.Paper.BoundedSiteCompositorConjugates | V1 | Same definitions and theorem statements; no edit. |
| lem-pur-bounded-site-exchange-transposes | Sheaf.Paper.BoundedSiteExchangeTransposes | D3 | Same definitions and theorem statements; no edit. |
| lem-pur-bounded-site-tensor-transposes | Sheaf.Paper.BoundedSiteTensorTransposes | V9 | Same definitions and theorem statements; no edit. |
| lem-pur-canonical-tate-arrow-naturality | Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-cartier-class-agreement | Sheaf.Paper.CartierClassAgreement | B7 | Same definitions and theorem statements; no edit. |
| lem-pur-cartier-relative-boundary-realization | Sheaf.Paper.CartierRelativeBoundaryRealization | H3 | Same definitions and theorem statements; no edit. |
| lem-pur-cartier-relative-kummer-realization | Sheaf.Paper.CartierRelativeKummerRealization | B8 | Same definitions and theorem statements; no edit. |
| lem-pur-cfiber-stalk | Sheaf.Paper.CompactFiberStalk | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-cartesian-domain | Sheaf.Paper.ChartCartesianDomain | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-diagonal-source-mate | Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-diagonal-source-square | Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-dnc-square | Sheaf.Paper.ChartDncSquare | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-dnc-vector-factors | Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-epsilon-pasting | Sheaf.Paper.ChartEpsilonPasting | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-exceptional-counit-equation | Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-exceptional-mate-coherence | Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-local-bounds | Sheaf.Paper.PurityChartLocalBounds | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-normal-differential | Sheaf.Paper.ChartNormalDifferential | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-normal-integration-square | Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chart-target-open-descent | Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-chern-flag-formula | Sheaf.Paper.ChernFlagFormula | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-classical-localization-triangle-transport | Sheaf.Paper.ClassicalLocalizationTriangleTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-augmented-integral-descent | Sheaf.Paper.AugmentedIntegralDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-common-compact-support | Sheaf.Paper.ClopenCommonCompactSupport | B3 | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-counit-adjoint-comparison | Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-exceptional-scalar-descent | Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-finite-constructibility-bounds | Sheaf.Paper.FiniteClopenConstructibilityBounds | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-roos-integral-descent | Sheaf.Paper.ClopenRoosIntegralDescent | C3 | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-strict-system-support | Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-clopen-system-integral-realization | Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-etale-transport-bounds | Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-finite-adjoint-counit-transport | Sheaf.Paper.ClosedFiniteAdjointCounitTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-section-compact-origin | Sheaf.Paper.ClosedSectionCompactOrigin | B9 | Same definitions and theorem statements; no edit. |
| lem-pur-closed-source-site-tensor-comparison | Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Same definitions and theorem statements; no edit. |
| lem-pur-closed-support-exceptional-comparison | Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-support-exceptional-mate | Sheaf.Paper.ClosedSupportExceptionalMate | C6 | Same definitions and theorem statements; no edit. |
| lem-pur-closed-supported-cup-vanishing | Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-transported-hom-counit-formula | Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-closed-unbounded-compact-support-normalization | Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-co-smooth-composition | Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-co-smooth-etale-locality | Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-common-stage-finite-hom-lifting | Sheaf.Paper.CommonStageFiniteHomLifting | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-common-stage-finite-object-lifting | Sheaf.Paper.CommonStageFiniteObjectLifting | U5 | Same definitions and theorem statements; no edit. |
| lem-pur-common-stage-restriction-tensor-descent | Sheaf.Paper.CommonStageRestrictionTensorDescent | U6 | Same definitions and theorem statements; no edit. |
| lem-pur-common-stage-smooth-operation-identification | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-product-proper-support-compatibility | Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-arrow-scalar-transport | Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-coefficient-models | Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-composite-transpose-domains | Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-integral-coefficient-comparison | Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-limit-equation-realization | Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-scalar-limit-reduction | Sheaf.Paper.CompactSupportScalarLimitReduction | Z5 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-scalar-projection-identification | Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-scalar-shift-normalization | Sheaf.Paper.CompactSupportScalarShiftNormalization | Q2 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-site-coherence | Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-strict-scalar-composition | Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-strict-scalar-mate | Sheaf.Paper.CompactSupportStrictScalarMate | A9 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-support-strict-scalar-refinement | Sheaf.Paper.CompactSupportStrictScalarRefinement | V7 | Same definitions and theorem statements; no edit. |
| lem-pur-compact-transpose-unit-naturality | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-compactification-b-projection-reduction | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-completed-unit-pullback-tower | Sheaf.Paper.CompletedUnitPullbackTower | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-completed-unit-scalar-naturality | Sheaf.Paper.CompletedUnitScalarNaturality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-composite-integration-counit | Sheaf.Paper.CompositeIntegrationCounit | A8 | Same definitions and theorem statements; no edit. |
| lem-pur-composition-comparison-scalar-compatibility | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-composition-compatible-dnc-charts | Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-composition-model-orientation-descent | Sheaf.Paper.CompositionModelOrientationDescent | V3 | Same definitions and theorem statements; no edit. |
| lem-pur-composition-tensor-mate | Sheaf.Paper.CompositionTensorMate | G8 | Same definitions and theorem statements; no edit. |
| lem-pur-concentrated-complex-shift | Sheaf.Paper.ConcentratedComplexShift | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-concentrated-support-etale-transfer | Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-constant-purity-frobenius-square | Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-constructible-tensor-composition | Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-coordinate-boundary-geometric-pullback | Sheaf.Paper.CoordinateBoundaryGeometricPullback | K2 | Same definitions and theorem statements; no edit. |
| lem-pur-coordinate-line-adjunction | Sheaf.Paper.CoordinateLineAdjunction | G9 | Same definitions and theorem statements; no edit. |
| lem-pur-coordinate-section-product-recursion | Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-coordinate-tower-normalization-induction | Sheaf.Paper.CoordinateTowerNormalizationInduction | K4 | Same definitions and theorem statements; no edit. |
| lem-pur-coprojection | Sheaf.Paper.PurityCoprojection | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-derived-local-class-edge-comparison | Sheaf.Paper.DerivedLocalClassEdgeComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-affine-trace-site-comparison | Sheaf.Paper.DiagonalAffineTraceSiteComparison | Z7 | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-base-change | Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-dnc-assembly-global | Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-dnc-chart-normalization | Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-ordinary-orientation-gluing | Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-ordinary-orientation-normalization | Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-ordinary-orientation-rigidity | Sheaf.Paper.DiagonalOrdinaryOrientationRigidity | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-orientation-choice-independent | Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-orientation-refinement | Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same definitions and theorem statements; no edit. |
| lem-pur-diagonal-section-pasting | Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-difference-coordinate-section-identifications | Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-divisor-class | Sheaf.Paper.PurityDivisorClass | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-divisor-normalized-realization | Sheaf.Paper.DivisorNormalizedRealization | E7 | Same definitions and theorem statements; no edit. |
| lem-pur-dnc-section-geometry | Sheaf.Paper.PurityDncComparisons | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-double-diagonal-section-identifications | Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-dualizing-sigma-cocycle-locality | Sheaf.Paper.DualizingSigmaCocycleLocality | D4 | Same definitions and theorem statements; no edit. |
| lem-pur-dualizing-unit-composite | Sheaf.Paper.DualizingUnitComposite | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-etale-cartesian-tower-tensor-comparison | Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-etale-closed-output-bounds | Sheaf.AlgebraicGeometry.EtaleClosedOutputBounds | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-etale-iso-descent | Sheaf.Paper.EtaleIsoDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-etale-witness-transport-data | Sheaf.Paper.EtaleWitnessTransportData | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-even-line-product-integration-symmetry | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-exceptional-base-change-pasting | Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-exceptional-mate-site-comparison | Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-adjoint-mate-compatibility | Sheaf.Paper.FiniteAdjointMateCompatibility | T3 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-clopen-derived-decomposition | Sheaf.Paper.FiniteClopenDerivedDecomposition | J5 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-clopen-exceptional-restriction | Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-diagonal-orientation-reduction | Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-dnc-normalization-reduction | Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-etale-dualizing-normalization | Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | N2 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-forward-product-symmetry | Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-free-compact-composition | Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-free-projection-exchange | Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-geometric-purity-mate | Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-kummer-level | Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-open-interval-descent | Sheaf.Paper.PurityFiniteOpenIntervalDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-open-product-swap | Sheaf.Paper.FiniteOpenProductSwap | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-product-compactification | Sheaf.Paper.FiniteProductCompactification | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-product-field-coefficient-descent | Sheaf.Paper.FiniteProductFieldCoefficientDescent | Y3 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-projection-action-laws | Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-proper-product-transpose | Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-setting-comparison-hypotheses | Sheaf.Paper.PurityFiniteSettingComparisonHypotheses | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-site-counit-projection-transport | Sheaf.Paper.FiniteSiteCounitProjectionTransport | U8 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-source-chart-scalar-transition | Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-tate-source-comparison-calculus | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-tate-source-structural-coherence | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-tensor-presentation-reduction | Sheaf.Paper.FiniteTensorPresentationReduction | E2 | Same definitions and theorem statements; no edit. |
| lem-pur-finite-triple-product-normal-forms | Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-twist-root-trivialization | Sheaf.Paper.FiniteTwistRootTrivialization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-type-coordinate-support-orientation | Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-finite-universal-smooth-trace | Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-flag-local-comparison | Sheaf.Paper.FlagLocalComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-flag-localized-product | Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-flag-pullback-injective | Sheaf.Paper.FlagPullbackInjective | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-gysin-structure | Sheaf.Paper.PurityGysinStructure | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-immersion-twist | WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-integral-coefficient-model-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-integral-geometric-comparison-realization | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-integral-orientation-reduction-injectivity | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-integral-scalar-isomorphism-exchange | Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-integration-exponent-transpose-transport | Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Same definitions and theorem statements; no edit. |
| lem-pur-isomorphism-exchange-scalar-refinement-descent | Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-isomorphism-finite-exchange-coherence | Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-isomorphism-finite-mate-normalization | Sheaf.Paper.IsomorphismFiniteMateNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-isomorphism-strict-integral-exchange-normalization | Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-iterated-purity-scalar-pasting | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-iterated-tate-source-composite | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-kummer-additivity | Sheaf.Paper.KummerAdditivity | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-kummer-coefficient-base-change | Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-kummer-product-shear-homotopy | Sheaf.Paper.KummerProductShearHomotopy | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-kummer-product-unit-permutation | Sheaf.Paper.KummerProductUnitPermutation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-kummer-triangle-concentration | Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-line-zero-class-etale-realization | Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-line-zero-class-exchange | Sheaf.Paper.LineZeroClassExchange | Z6 | Same definitions and theorem statements; no edit. |
| lem-pur-line-zero-geometry | Sheaf.Paper.LineZeroGeometry | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-lisse-morphism-rigidity | Sheaf.Paper.PurLisseMorphismRigidity | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-lisse-rank-one-aut | Sheaf.Paper.LisseRankOneAut | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-lisse-uniqueness | Sheaf.Paper.PurityLisseUniqueness | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-normal-model-section-orientation | Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordered-affine-transpose-projection | Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordinary-derived-composite-transpose | Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordinary-derived-isomorphism-transport-transpose | Sheaf.Paper.OrdinaryDerivedIsomorphismTransportTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordinary-derived-product-leg-transposes | Sheaf.Paper.OrdinaryDerivedProductLegTransposes | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordinary-triple-product-transpose | Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-ordinary-unit-exchange-naturality | Sheaf.Paper.OrdinaryUnitExchangeNaturality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-orientation-ground-field-retagging | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-p1-kummer-trace-site-transport | Sheaf.Paper.P1KummerTraceSiteTransport | W8 | Same definitions and theorem statements; no edit. |
| lem-pur-pf-finite-compositor-counit | Sheaf.Paper.FiniteCompositorCounit | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-pf-refinement-compatibility | Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-pf-witnessed-mate-normalization | Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-point-trace-reconstruction | Sheaf.Paper.PointTraceReconstruction | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-product-exchange-counit-coordinates | Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-product-forward-coordinate-transport | Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-product-open-tensor-projection | Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-proetale-direct-image-global-evaluation | Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-projection-purity-agreement | Sheaf.Paper.ProjectionPurityAgreement | N2 | Same definitions and theorem statements; no edit. |
| lem-pur-rational-lattice-adic-domain | Sheaf.Paper.RationalLatticeAdicDomain | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-rational-normalized-purity-diagrams | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-rational-purity-exchange-endpoints | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-rational-restriction-comparison-coherence | Sheaf.Paper.RationalRestrictionComparisonCoherence | X7 | Same definitions and theorem statements; no edit. |
| lem-pur-rational-scalar-comparison-identification | Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Same definitions and theorem statements; no edit. |
| lem-pur-rationalized-smooth-adjunction-diagrams | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-raw-condensed-rational-adjunction-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-regular-immersion-linearization | Sheaf.AlgebraicGeometry.RegularImmersionLinearization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-regular-immersion-smooth-structure | WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-external-power-regrouping | Sheaf.Paper.RelativeExternalPowerRegrouping | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-kummer-coefficient-normalization | Sheaf.Paper.RelativeKummerCoefficientNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-product-geometric-factors | Sheaf.Paper.RelativeProductGeometricFactors | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-support-bottom-descent | Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-support-coordinate-model | Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-relative-support-vanishing | Sheaf.Paper.RelativeSupportVanishing | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-retagging-coefficient-tower-transfer | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-retagging-coordinate-orientations | Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-retracted-support-localization-comparison | Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-section-etale-restriction-coherence | Sheaf.Paper.PuritySectionEtaleRestriction | Y2 | Same definitions and theorem statements; no edit. |
| lem-pur-shifted-line-site-inverse | Sheaf.Paper.ShiftedLineSiteInverse | P1 | Same definitions and theorem statements; no edit. |
| lem-pur-shifted-tate-unit-scalar-coherence | Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-signed-twist-site-transport | Sheaf.Paper.SignedTwistSiteTransport | A6 | Same definitions and theorem statements; no edit. |
| lem-pur-smb-extraordinary | Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-smb-mate-counit-cancellation | Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-smooth-exceptional-tensor-pasting | Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Same definitions and theorem statements; no edit. |
| lem-pur-smooth-exchange-scalar-compatibility | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-strict-reduction-compact-support-normalization | Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-affine-line-homotopy | Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-bottom-gluing | Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-class-evaluation-comparison | Sheaf.Paper.SupportedClassEvaluationComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-constant-exchange-normalization | Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-cup-functoriality | Sheaf.Paper.SupportedCupFunctoriality | Q8 | Same definitions and theorem statements; no edit. |
| lem-pur-supported-hom | Sheaf.Paper.SupportedCohomologyHom | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-hom-adjunction-transpose | Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-hom-cocycle-normalization | Sheaf.Paper.SupportedHomCocycleNormalization | F2 | Same definitions and theorem statements; no edit. |
| lem-pur-supported-hom-pullback | Sheaf.Paper.SupportedHomPullback | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-root-scalar-site-comparison | Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | Same definitions and theorem statements; no edit. |
| lem-pur-supported-sections-hom | Sheaf.Paper.SupportedSectionsHom | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-supported-tensor-isomorphism-transport | Sheaf.Paper.SupportedTensorIsomorphismTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tate-source-field-comparison-descent | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tate-source-strict-system-identities | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tate-unit-flat-model-domains | Sheaf.Paper.PurTateUnitFlatModelDomains | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tensor-map-naturality | Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tensor-map-presentation-independent | Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tensor-mate-base-change | Sheaf.Paper.TensorMateBaseChange | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tensor-mate-invertible-input | Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tensor-trace-transpose | Sheaf.Paper.TensorTraceTranspose | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-geometric-purity-mate | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-operations-ground-field-retagging | Sheaf.Paper.TowerOperationsGroundFieldRetagging | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-purity-ground-field-retagging | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-purity-realized-transpose | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-tensor-transpose-ground-field-retagging | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-tower-trace-purity-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-trace-transpose-base-change | Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-transport-finite-counit-system | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-transport-integral-counit-realization | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-transport-qbar-common-stage-counit | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-transport-rational-hom-counit | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-twisted-coordinate-section-normalization | Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-twisted-pullback-square-scalars | Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-two-open-tensor-chain-normalization | Sheaf.Paper.TwoOpenTensorChainNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-unit-kummer-two-site-normalization | Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same definitions and theorem statements; no edit. |
| lem-pur-unshifted-line-unit-tower | Sheaf.Paper.UnshiftedLineUnitTower | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-varying-dimension-dualizing-inverse | Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-vector-bundle-frame-orientation-restriction | Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-vector-frame-integration-site-descent | Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Same definitions and theorem statements; no edit. |
| lem-pur-vector-integration-chart-comparison | Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-vector-integration-site-comparison | Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-vector-model-chart-descent | Sheaf.Paper.VectorModelChartDescent | T9 | Same definitions and theorem statements; no edit. |
| lem-pur-weil-basechange-diagram-identifications | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-basechange-semilinear-pasting | Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-coefficient-diagram-identifications | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-composite-diagram-identifications | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-kappa-coefficient-coherence | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-semilinear-exchange-reindexing | Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-weil-tate-datum-transport | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-witnessed-open-chart-transport | Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-pur-zero-support-retraction-triangle | Sheaf.Paper.PurityZeroSupportRetractionTriangle | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sf-locally-closed-relative-transpose-normalization | Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-exceptional-system-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-orientation-system-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-projection-origin-witnesses | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-projection-system-square | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-purity-system-transpose | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-scalar-normalized-systems | Sheaf.Paper.FieldScalarNormalizedSystems | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-field-shriek-system-comparison | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-sp-section-dnc-integration-square | Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same definitions and theorem statements; no edit. |
| lem-trf-constant-complex-a1-morphism-rigidity | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| lem-trf-finite-structural-maps-commshift | Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same definitions and theorem statements; no edit. |
| lem-weil-boundary-comparison-composition-transport | Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same definitions and theorem statements; no edit. |
| lem-weil-proper-finite-normalization | Sheaf.Paper.ProperFiniteNormalization | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-a1-invariance | Sheaf.Paper.AffineLineInvariance | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-adic-reconstruction-trace-coherence | WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-affine-line-orientation-base-change | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-affine-line-orientation-uniqueness | Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-affine-space-composition-law | Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-dnc-family-constancy | WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-gm-relative-kummer | Sheaf.Paper.PurityRelativeKummer | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-rational-purity-trace-coherence | Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| prop-pur-regular-immersion-purity-compatibilities | WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Same definitions and theorem statements; no edit. |
| pur9-cs-def-bc | Sheaf.Paper.StandingExceptionalBaseChangeCompared | unclaimed | Same definitions and theorem statements; no edit. |
| pur9-def-upper-shriek-composition | Sheaf.Paper.StandingExceptionalComposition | unclaimed | Same definitions and theorem statements; no edit. |
| pur9-rg-def-phi | Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same definitions and theorem statements; no edit. |
| sk-def-purity-conv | Sheaf.Paper.PurityConventions | V4 | Same definitions and theorem statements; no edit. |
| sk-lem-sp-field-extension | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| sk-thm-dnc | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| sk-thm-purity-transport | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-adic-reconstruction | Sheaf.Paper.PurAdicReconstruction | S2 | Same definitions and theorem statements; no edit. |
| thm-pur-affine-line-orientation | Sheaf.Paper.PurityAffineLineOrientation | C4 | Same definitions and theorem statements; no edit. |
| thm-pur-affine-line-purity | WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-cohomological-smoothness | Sheaf.Paper.CohomologicalSmoothnessTheorem | V8 | Same definitions and theorem statements; no edit. |
| thm-pur-composition-coherence | Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-diagonal-dualizing-object | Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-dnc-invariance | Sheaf.Paper.PurityDncInvariance | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-finite-coefficient-smooth-purity | Sheaf.Paper.FiniteCoefficientSmoothPurity | H1 | Same definitions and theorem statements; no edit. |
| thm-pur-finite-reduction-of-purity | Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-general-admissibility | Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-localized-top-chern | Sheaf.Paper.LocalizedTopChern | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-open-complement-unconditional | Sheaf.Paper.OpenComplementUnconditional | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-projective-bundle-formula | Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-rank-one-local-calculation | Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-rank-one-thom | WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-rational-and-qbar-purity | Sheaf.Paper.RationalSmoothPurityCanonical | M2 | Same definitions and theorem statements; no edit. |
| thm-pur-regular-immersion-purity | Sheaf.Paper.RegularImmersionPurity | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-smooth-base-change-coherence | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-td-criterion | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-trace-normalization-transitivity | WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-vector-bundle-thom | Sheaf.Paper.VectorBundleThom | unclaimed | Same definitions and theorem statements; no edit. |
| thm-pur-weil-equivariance-of-purity-and-trace | (no Lean attachment) | unclaimed | Same definitions and theorem statements; no edit. |

## Status

landed 20261025T123847-L-1909976 2026-10-25 (merge of deliver/T1/Sheaf.SixFunctors.IntegralBasicRealization)
